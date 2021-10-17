{-# LANGUAGE MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           , TypeSynonymInstances
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-deprecations #-}
----------------------------------------------------------------
--                                                  ~ 2021.10.17
-- |
-- Module      :  PuttingHR
-- Copyright   :  Copyright (c) 2007--2021 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@cpan.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An implementation of higher-ranked type checking a la Peyton
-- Jones, Vytiniotis, Weirich, and Shields /Practical type inference/
-- /for arbitrary-rank types/ using the unification-fd library. This
-- is mainly here for testing and debugging, rather than for actual
-- use.
----------------------------------------------------------------
module Putting where

import Prelude hiding
    ( mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1
    , any, all, and, or, elem, concat
    )
import qualified Data.Map as M
import Data.List ((\\))
import Data.Maybe (fromMaybe)
import Data.IORef
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad          (liftM)
import Control.Monad.Error    (Error(..), MonadError(..), ErrorT(..))
import Control.Monad.Reader   (MonadReader(..), asks, ReaderT(..), runReaderT)
import Control.Monad.Trans    (MonadTrans(..))
import Control.Unification    hiding (unify, lookupVar)
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

type Name = String

-- To add multi-branch constructs like case and conditionals, see "unification under a mixed prefix" for typing it <Miller 1992> etc. However, apparently that will type fewer programs than using the equivalence relation induced by two-way subsumption... It also looses the property that if $\Gamma' \vdash^{poly}_\Downarrow t : \sigma$ and $\vdash^{dsk} \Gamma \leq \Gamma'$ then $\Gamma \vdash^poly_\Downarrow t : \sigma$. (Though the checkingness can be regained by adding type annotations.)
data Term
    = Var Name             -- ^ @x@
    | Lit Int              -- ^ @3@
    | App Term Term        -- ^ @f x@
    | Lam Name Term        -- ^ @\x. x@
    | ALam Name Sigma Term -- ^ @\(x::t). x@
    | Let Name Term Term   -- ^ @let x = f y in x+1@
    | Ann Term Sigma       -- ^ @x :: t@
    deriving (Show)

----------------------------------------------------------------

type Sigma = Type
type Rho   = Type -- ^ No top-level @ForAll@
type Tau   = Type -- ^ No @ForAll@s anywhere
type Type  = UTerm Ty MetaTv
data Ty t
    = ForAll [TyVar] t   -- ^ Forall type
    | Fun t t            -- ^ Function type
    | TyCon TyCon        -- ^ Type constants
    | TyVar TyVar        -- ^ Always bound by a @ForAll@
    deriving (Show, Functor, Foldable, Traversable)

-- | Invariant: metas can only be bound to 'Tau'
type MetaTv = IntVar

data TyVar
    = BoundTv  Name      -- ^ A type variable bound by a @ForAll@
    | SkolemTv Name Uniq -- ^ A skolem constant; the Name is just to improve error messages
    deriving (Show, Eq)

type Uniq = Int

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

-- | Directionalities for rules which are polymorphic in checking
-- vs inference.
data Expected t
    = Check t
    | Infer (TcRef t)

type TcRef a = IORef a -- TODO: replace by IVar, or something else closer to truth. (or break our invariant and just use a metavariable)

newTcRef :: a -> Tc (TcRef a)
newTcRef = TC . lift . lift . lift . newIORef -- TODO: liftIO or liftBase

-- TODO: throw errors on writing twice.
writeTcRef :: TcRef a -> a -> Tc ()
writeTcRef = ((TC . lift . lift . lift) .) . writeIORef

readTcRef :: TcRef a -> Tc a
readTcRef = TC . lift . lift . lift . readIORef

----------------------------------------------------------------

type TCState = M.Map Name Type

data TCFailure
    = OccursFailure    IntVar (UTerm Ty IntVar)
    | MismatchFailure  (Ty (UTerm Ty IntVar)) (Ty (UTerm Ty IntVar))
    | CheckFailure     String
    | LookupVarFailure Name
    deriving (Show)

instance Fallible Ty IntVar TCFailure where
    occursFailure   = OccursFailure
    mismatchFailure = MismatchFailure

instance Error TCFailure where
    noMsg  = CheckFailure ""
    strMsg = CheckFailure

-- | The type-checker monad.
newtype Tc a =
    TC { unTC ::
        ReaderT TCState         -- Gamma: types for term-variables
            (ErrorT TCFailure   -- possibility for failure
                (IntBindingT Ty -- unification metavariables
                    IO))        -- TcRefs for the inference direction
            a }
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader TCState
        , MonadError  TCFailure
        )


evalTC :: Tc a -> IO (Either TCFailure a)
evalTC
    = evalIntBindingT
    . runErrorT
    . flip runReaderT M.empty
    . unTC


-- | Type inference can fail.
check :: Bool -> String -> Tc ()
check True  _   = return ()
check False msg = throwError $ CheckFailure msg


-- | Look up a 'Var' in Gamma to get its type.
lookupVar :: Name -> Tc Sigma
lookupVar x = do
    mb <- asks (M.lookup x)
    case mb of
        Just t  -> return t
        Nothing -> throwError $ LookupVarFailure x


-- | Extend Gamma locally.
extendVarEnv :: Name -> Sigma -> Tc a -> Tc a
extendVarEnv x t m = local (M.insert x t) m


-- | Get Gamma.
getEnvTypes :: Tc [Sigma]
getEnvTypes = liftM M.elems ask


-- | Unify two types. Unification only affects metavariables.
unify :: Tau -> Tau -> Tc ()
unify tl tr = TC $ lift (tl =:= tr >> return ())


-- | Make a fresh metavariable.
newMetaTyVar :: Tc Tau
newMetaTyVar = TC . liftM UVar . lift $ lift freeVar


-- | Make a fresh skolem TyVar for some given TyVar
newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv = liftM (SkolemTv $ tyVarName tv) newUnique
    where
    -- HACK: this became ambiguous since 2012, thus requiring the inline signature on getVarID...
    newUnique :: Tc Uniq
    newUnique = TC . lift . lift $ liftM (getVarID :: IntVar -> Int) freeVar

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

-- | The plain infer-turnstile.
inferRho :: Term -> Tc Rho
inferRho expr = do
    ref <- newTcRef (error "inferRho: empty result")
    tcRho expr (Infer ref)
    readTcRef ref


-- | The plain check-turnstile.
-- Invariant: 'Rho' is in weak-prenex form.
checkRho :: Term -> Rho -> Tc ()
checkRho expr ty = tcRho expr (Check ty)


-- We replace 'unify' with 'instSigma' because the latter deals
-- with Expecteds.
-- | The plain delta-turnstile.
-- Invariant: if the Expected is @Check ty@ then @ty@ is in weak-prenex
-- form.
tcRho :: Term -> Expected Rho -> Tc ()
tcRho (Lit _) exp_ty =
    instSigma intType exp_ty
tcRho (App fun arg) exp_ty = do
    fun_ty <- inferRho fun
    (arg_ty, res_ty) <- unifyFun fun_ty
    checkSigma arg arg_ty
    instSigma res_ty exp_ty
tcRho (Lam var body) (Infer ref) = do
    var_ty  <- newMetaTyVar
    body_ty <- extendVarEnv var var_ty (inferRho body)
    writeTcRef ref (var_ty ==> body_ty)
tcRho (Lam var body) (Check exp_ty) = do
    (pat_ty, body_ty) <- unifyFun exp_ty
    extendVarEnv var pat_ty (checkRho body body_ty)
    -- N.B., we can checkRho instead of checkSigma because of tcRho's
    -- invariant
tcRho (ALam var var_ty body) (Infer ref) = do
    body_ty <- extendVarEnv var var_ty (inferRho body)
    writeTcRef ref (var_ty ==> body_ty)
tcRho (ALam var var_ty body) (Check exp_ty) = do
    (arg_ty, body_ty) <- unifyFun exp_ty
    subsCheck arg_ty var_ty
    extendVarEnv var var_ty (checkRho body body_ty)
tcRho (Var v) exp_ty = do
    v_sigma <- lookupVar v
    instSigma v_sigma exp_ty
tcRho (Let v rhs body) exp_ty = do
    v_sigma <- inferSigma rhs
    extendVarEnv v v_sigma (tcRho body exp_ty)
tcRho (Ann body ann_ty) exp_ty = do
    checkSigma body ann_ty
    instSigma ann_ty exp_ty
{-
tcRho (If e1 e2 e3) (Check rho) = do
    checkRho e1 boolType
    checkRho e2 rho
    checkRho e3 rho
-- Use the equivalence relation induced by subsumption
tcRho (If e1 e2 e3) (Infer ref) = do
    checkRho e1 boolType
    rho1 <- inferRho e2
    rho2 <- inferRho e3
    subsCheck rho1 rho2
    subsCheck rho2 rho1
    writeTcRef ref rho1 -- Arbitrarily choose rho1 instead of rho2. This infelicity could be circumvented by skolemising the return type and re-generalising at the top-level all of its quantified variables.
-}


unifyFun :: Rho -> Tc (Rho, Rho)
unifyFun (UTerm(Fun arg_ty res_ty)) = return (arg_ty, res_ty)
unifyFun fun_ty = do
    arg_ty <- newMetaTyVar
    res_ty <- newMetaTyVar
    unify fun_ty (arg_ty ==> res_ty)
    return (arg_ty,res_ty)


-- N.B., that we can use subsCheckRho in lieu of subsCheck relies
-- on the invariant.
-- | The inst-delta-turnstile.
-- Invariant: if the Expected is @Check ty@ then @ty@ is in weak-prenex
-- form.
instSigma :: Sigma -> Expected Rho -> Tc ()
instSigma sigma (Infer ref) = writeTcRef ref =<< instantiate sigma
instSigma sigma (Check rho) = subsCheckRho sigma rho


-- | The poly-check-turnstile. This is the (plain) SKOL rule,
-- formerly a part of 'subsCheck'.
checkSigma :: Term -> Sigma -> Tc ()
checkSigma expr sigma = do
    (skol_tvs, rho) <- skolemise sigma
    checkRho expr rho
    env_tys <- getEnvTypes
    esc_tvs <- getFreeTyVars (sigma : env_tys)
    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    check (null bad_tvs) "Type not polymorphic enough"


-- | The poly-infer-turnstile.
inferSigma :: Term -> Tc Sigma
inferSigma e = do
    res_ty  <- inferRho e
    env_tys <- getEnvTypes
    env_tvs <- getMetaTyVars env_tys
    res_tvs <- getMetaTyVars [res_ty]
    let forall_tvs = res_tvs \\ env_tvs -- -> -- BUG: syntax hilighting
    quantify forall_tvs res_ty
    {-
    where
    -- This all is no longer necessary. Just use (Data.List.\\)
    minus xs ys = filter (\x -> not $ elemBy eqVar x ys) xs

    -- From "Data.List", though it's not exported for some reason...
    elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
    elemBy _  _ []         =  False
    elemBy eq y (x:xs)     =  y `eq` x || elemBy eq y xs
    -}


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


-- | The dsk*-turnstile, our \"super-unifier\".
-- Invariant: Rho is in weak-prenex form.
subsCheckRho :: Sigma -> Rho -> Tc ()
subsCheckRho sigma1@(UTerm(ForAll _ _)) rho2 = do -- Rule SPEC/INST
    rho1 <- instantiate sigma1
    subsCheckRho rho1 rho2
-- N.B., because of the invariant, we don't check ForAll on the second arg
subsCheckRho t1 (UTerm(Fun a2 r2)) = do
    (a1,r1) <- unifyFun t1
    subsCheckFun a1 r1 a2 r2
subsCheckRho (UTerm(Fun a1 r1)) t2 = do
    (a2,r2) <- unifyFun t2
    subsCheckFun a1 r1 a2 r2
subsCheckRho tau1 tau2 = do -- Rule MONO
    unify tau1 tau2 -- Revert to ordinary unification


subsCheckFun :: Sigma -> Rho -> Sigma -> Rho -> Tc ()
subsCheckFun arg1 res1 arg2 res2 = do -- Rule FUN
    subsCheck arg2 arg1
    subsCheckRho res1 res2


-- | The dsk-turnstile, our \"super-unifier\".
subsCheck :: Sigma -> Sigma -> Tc ()
subsCheck sigma1 sigma2 = do -- Rule DEEP-SKOL
    (skol_tvs, rho2) <- skolemise sigma2
    subsCheckRho sigma1 rho2
    esc_tvs <- getFreeTyVars [sigma1,sigma2] -- because sigma2 is not closed.
    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    check (null bad_tvs) "Subsumption check failed:..."
        {-
        (vcat
        [ text "Subsumption check failed:"
        , nest 2 (ppr sigma1)
        , text "is not as polymorphic as"
        , nest 2 (ppr sigma2)
        ])
        -}


-- | Instantiate the topmost ForAlls of the argument type with
-- flexible type variables.
instantiate :: Sigma -> Tc Rho
instantiate (UTerm(ForAll tvs ty)) = do
    tvs' <- mapM (\_ -> newMetaTyVar) tvs
    return (substTy tvs tvs' ty)
instantiate ty = return ty


-- | The function pr(sigma).
skolemise :: Sigma -> Tc ([TyVar], Rho)
skolemise (UTerm(ForAll tvs ty))     = do -- Rule PRPOLY
    sks1        <- mapM newSkolemTyVar tvs
    (sks2, ty') <- skolemise (substTy tvs (map (UTerm . TyVar) sks1) ty)
    return (sks1 ++ sks2, ty')
skolemise (UTerm(Fun arg_ty res_ty)) = do -- Rule PRFUN
    (sks, res_ty') <- skolemise res_ty
    return (sks, UTerm$Fun arg_ty res_ty')
skolemise ty                         = do -- Rule PRMONO
    return ([], ty)


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

----------------------------------------------------------------
----------------------------------------------------------- fin.
