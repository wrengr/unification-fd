{-# LANGUAGE MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           , TypeSynonymInstances
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2012.03.25
-- |
-- Module      :  PuttingDM
-- Copyright   :  Copyright (c) 2007--2012 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An implementation of Hindley--Damas--Milner a la Peyton Jones,
-- Vytiniotis, Weirich, and Shields /Practical type inference for/
-- /arbitrary-rank types/ using the unification-fd library. This
-- is mainly here for testing and debugging, rather than for actual
-- use.
----------------------------------------------------------------
module Putting where

import Prelude hiding
    ( mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1
    , any, all, and, or, elem
    )
import qualified Data.Map as M
import Data.List  ((\\))
import Data.Maybe (fromMaybe)
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad          (liftM)
import Control.Monad.Error    (MonadError(..), ErrorT(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Reader   (MonadReader(..), asks, ReaderT(..), runReaderT)
import Control.Monad.Trans    (MonadTrans(..))
import Control.Unification    hiding (unify, lookupVar)
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

type Name = String 
type Uniq = Int 
data Term
    = Var Name             -- x
    | Lit Int              -- 3
    | App Term Term        -- f x
    | Lam Name Term        -- \x. x
    | Let Name Term Term   -- let x = f y in x+1
    | Ann Term Sigma       -- x :: t
    deriving (Show)

type Sigma = Type 
type Rho   = Type -- No top-level ForAll
type Tau   = Type -- No ForAlls anywhere
type Type  = UTerm Ty MetaTv
data Ty t
    = ForAll [TyVar] t   -- Forall type
    | Fun t t            -- Function type
    | TyCon TyCon        -- Type constants
    | TyVar TyVar        -- Always bound by a ForAll
    deriving (Show, Functor, Foldable, Traversable)
type MetaTv = IntVar     -- N.B., invariant: metas can only be bound to Tau!
data TyVar
    = BoundTv  Name      -- A type variable bound by a ForAll
    | SkolemTv Name Uniq -- A skolem constant; the Name is just to improve error messages
    deriving (Show, Eq)
data TyCon
    = IntT
    | BoolT 
    deriving (Show, Eq)

-- | Build a function type (abstractly).
(==>) :: Type -> Type -> Type
arg ==> res = UTerm (Fun arg res)

-- | The integer type (abstractly).
intType :: Tau
intType = UTerm (TyCon IntT)

-- | The boolean type (abstractly).
boolType :: Tau
boolType = UTerm (TyCon BoolT)

instance Unifiable Ty where
    zipMatch (ForAll vls tl) (ForAll vrs tr)
        | and $ zipWith (==) vls vrs = Just $ ForAll vls (Right(tl,tr))
    
    zipMatch (Fun tl1 tl2) (Fun tr1 tr2)
        = Just $ Fun (Right(tl1,tr1)) (Right(tl2,tr2))
    
    zipMatch (TyCon cl) (TyCon cr)
        | cl == cr = Just $ TyCon cl
    
    zipMatch (TyVar vl) (TyVar vr)
        | vl == vr = Just $ TyVar vl
    
    zipMatch _ _ = Nothing

----------------------------------------------------------------

type TCState = M.Map Name Type
type TCError = UnificationFailure Ty IntVar

-- | The type-checker monad.
newtype Tc a =
    TC { unTC ::
        ReaderT TCState         -- Gamma: types for term-variables
            (ErrorT TCError     -- possibility for failure
                (IntBindingT Ty -- unification metavariables
                    Identity))
            a }
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader TCState
        , MonadError  TCError
        )


evalTC :: Tc a -> Either TCError a
evalTC
    = runIdentity
    . evalIntBindingT
    . runErrorT
    . flip runReaderT M.empty
    . unTC


-- | Type inference can fail.
check :: Bool -> String -> Tc ()
check True  _   = return ()
check False msg = throwError $ UnknownError msg


-- | Look up a 'TyVar' in Gamma.
lookupVar :: Name -> Tc Sigma
lookupVar x = do
    mb <- asks $ M.lookup x
    case mb of
        Nothing -> throwError . UnknownError $ "variable not found: " ++ show x
        Just t  -> return t


-- | Extend Gamma locally.
extendVarEnv :: Name -> Sigma -> Tc a -> Tc a
extendVarEnv x t m = local (M.insert x t) m


-- | Get Gamma.
getEnvTypes :: Tc [Sigma]
getEnvTypes = liftM M.elems ask


unify :: Tau -> Tau -> Tc ()
unify tl tr = TC $ lift (tl =:= tr >> return ())


-- | Make (MetaTv tv), where tv is fresh
newMetaTyVar :: Tc Tau
newMetaTyVar = TC . liftM UVar . lift $ lift freeVar


-- | Make a fresh skolem TyVar for some given TyVar
newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv = liftM (SkolemTv $ tyVarName tv) newUnique
    where
    newUnique :: Tc Uniq
    newUnique = TC . lift . lift $ liftM getVarID freeVar
    
    tyVarName :: TyVar -> Name
    tyVarName (BoundTv  name)   = name
    tyVarName (SkolemTv name _) = name


-- | Return the free metavariables in the list of types.
getMetaTyVars :: [Type] -> Tc [MetaTv]
getMetaTyVars = TC . lift . lift . getFreeVarsAll


-- | Return all the free type-variables in the list of types. (The
-- free ones must be Skolems.) This is monadic because it respects
-- the metavariable bindings.
getFreeTyVars :: [Type] -> Tc [TyVar]
getFreeTyVars = undefined
{-
getFreeTyVars = liftM freeTyVars . mapM zonkType
-}

----------------------------------------------------------------

inferRho :: Term -> Tc Rho
{-
-- Algorithm W:
inferRho (Lit _)       = return intType
inferRho (App fun arg) = do
    fun_ty <- inferRho fun
    arg_ty <- inferRho arg
    res_ty <- newMetaTyVar
    unify fun_ty (arg_ty ==> res_ty)
    return res_ty
...

-- Algorithm M:
-}
inferRho expr = do
    exp_ty <- newMetaTyVar
    checkRho expr exp_ty
    return exp_ty


checkRho :: Term -> Rho -> Tc ()

checkRho (Lit _) exp_ty =
    unify intType exp_ty

checkRho (App fun arg) exp_ty = do
    fun_ty <- inferRho fun
    (arg_ty, res_ty) <- unifyFun fun_ty
    checkRho arg arg_ty
    unify res_ty exp_ty

checkRho (Lam var body) exp_ty = do
    (pat_ty, body_ty) <- unifyFun exp_ty
    extendVarEnv var pat_ty (checkRho body body_ty)

checkRho (Var v) exp_ty = do
    v_sigma <- lookupVar v
    instSigma v_sigma exp_ty

checkRho (Let v rhs body) exp_ty = do
    v_sigma <- inferSigma rhs
    extendVarEnv v v_sigma (checkRho body exp_ty)

checkRho (Ann body ann_ty) exp_ty = do
    body_ty <- inferSigma body
    subsCheck body_ty ann_ty
    instSigma ann_ty exp_ty


unifyFun :: Rho -> Tc (Rho, Rho)
unifyFun (UTerm(Fun arg_ty res_ty)) = return (arg_ty, res_ty)
unifyFun fun_ty = do
    arg_ty <- newMetaTyVar
    res_ty <- newMetaTyVar
    unify fun_ty (arg_ty ==> res_ty)
    return (arg_ty,res_ty)


instSigma :: Sigma -> Rho -> Tc ()
instSigma sigma exp_ty = do
    rho <- instantiate sigma
    unify rho exp_ty


inferSigma :: Term -> Tc Sigma
inferSigma e = do
    res_ty  <- inferRho e
    env_tys <- getEnvTypes
    env_tvs <- getMetaTyVars env_tys
    res_tvs <- getMetaTyVars [res_ty]
    let forall_tvs = res_tvs \\ env_tvs -- -> -- BUG: syntax highlighting
    quantify forall_tvs res_ty


subsCheck :: Type -> Type -> Tc ()

subsCheck sigma1 sigma2@(UTerm(ForAll _ _)) = do -- Rule SKOL
    (skol_tvs, rho2') <- skolemise sigma2
    subsCheck sigma1 rho2'
    esc_tvs <- getFreeTyVars [sigma1]
    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    check (null bad_tvs) "Type not polymorphic enough"

subsCheck sigma1@(UTerm(ForAll _ _)) rho2 = do -- Rule INST
    rho1' <- instantiate sigma1
    subsCheck rho1' rho2

subsCheck rho1 rho2 = -- Rule MONO
    unify rho1 rho2


-- | Instantiate the topmost ForAlls of the argument type with
-- flexible type variables.
instantiate :: Sigma -> Tc Rho
instantiate (UTerm(ForAll tvs ty)) = do
    tvs' <- mapM (\_ -> newMetaTyVar) tvs
    return (substTy tvs tvs' ty)
instantiate ty = return ty


skolemise :: Sigma -> Tc ([TyVar], Rho)
skolemise (UTerm(ForAll tvs ty)) = do
    sks <- mapM newSkolemTyVar tvs
    return (sks, substTy tvs (map (UTerm . TyVar) sks) ty)
skolemise ty = return ([], ty)


type Env = [(TyVar, Tau)] 

-- Replace the specified quantified type variables by
-- given meta type variables
-- No worries about capture, because the two kinds of type
-- variable are distinct
substTy :: [TyVar] -> [Type] -> Type -> Sigma
substTy tvs tys ty = go (tvs `zip` tys) ty
    where
    go :: Env -> Type -> Type
    go env (UTerm(Fun arg res))   = UTerm$Fun (go env arg) (go env res)
    go env (UTerm(TyVar n))       = fromMaybe (UTerm$TyVar n) (lookup n env)
    go _   (UVar tv)              = UVar tv
    go _   (UTerm(TyCon tc))      = UTerm$TyCon tc
    go env (UTerm(ForAll ns rho)) = UTerm$ForAll ns (go env' rho)
        where
        env' = [(n,ty') | (n,ty') <- env, not (n `elem` ns)]

-- Quantify over the specified type variables (all flexible)
quantify :: [MetaTv] -> Rho -> Tc Sigma
quantify = undefined
{-
-- Not in scope: zonkType, tyVarBndrs, allBinders, writeTv
quantify tvs ty = do
    mapM_ bind (tvs `zip` new_bndrs) -- 'bind' is just a cunning way
    ty' <- zonkType ty               -- of doing the substitution
    return (ForAll new_bndrs ty')
    where
    used_bndrs = tyVarBndrs ty -- Avoid quantified type variables in use
    new_bndrs = take (length tvs) (allBinders \\ used_bndrs)
    bind (tv, name) = writeTv tv (TyVar name)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
