
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.11
-- |
-- Module      :  Control.Unification
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (MPTCs, FlexibleContexts)
--
-- This module provides first-order structural unification over
-- general structure types. It also provides the standard suite of
-- functions accompanying unification (applying bindings, getting
-- free variables, etc.).
--
-- The implementation makes use of numerous optimization techniques.
-- First, we use path compression everywhere (for weighted path
-- compression see "Control.Unification.Ranked"). Second, we replace
-- the occurs-check with visited-sets. Third, we use a technique
-- for aggressive opportunistic observable sharing; that is, we
-- track as much sharing as possible in the bindings (without
-- introducing new variables), so that we can compare bound variables
-- directly and therefore eliminate redundant unifications.
----------------------------------------------------------------
module Control.Unification
    (
    -- * Data types, classes, etc
    -- ** Mutable terms
      MutTerm(..)
    , freeze
    , unfreeze
    -- ** Errors
    , UnificationFailure(..)
    -- ** Basic type classes
    , Unifiable(..)
    , Variable(..)
    , BindingMonad(..)
    
    -- * Operations on one term
    , getFreeVars
    , applyBindings
    , freshen
    -- freezeM     -- apply bindings and freeze in one traversal
    -- unskolemize -- convert Skolemized variables to free variables
    -- skolemize   -- convert free variables to Skolemized variables
    -- getSkolems  -- compute the skolem variables in a term; helpful?
    
    -- * Operations on two terms
    -- ** Symbolic names
    , (===)
    , (=~=)
    , (=:=)
    , (<:=)
    -- ** Textual names
    , equals
    , equiv
    , unify
    , unifyOccurs
    , subsumes
    
    -- * Helper functions
    -- | Client code should not need to use these functions, but
    -- they are exposed just in case they are needed.
    , fullprune
    , semiprune
    , occursIn
    ) where

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, and, or)

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad       (MonadPlus(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Error (MonadError(..))
import Control.Monad.State (MonadState(..), StateT, evalStateT, execStateT)
import Control.Monad.MaybeK
import Control.Monad.State.UnificationExtras
import Control.Unification.Types
----------------------------------------------------------------
----------------------------------------------------------------

-- BUG: this assumes there are no directly-cyclic chains!
--
-- | Canonicalize a chain of variables so they all point directly
-- to the term at the end of the chain (or the free variable, if
-- the chain is unbound), and return that end.
--
-- N.B., this is almost never the function you want. Cf., 'semiprune'.
fullprune :: (BindingMonad v t m) => MutTerm v t -> m (MutTerm v t)
fullprune t0 =
    case t0 of
    MutTerm _ -> return t0
    MutVar  v -> do
        mb <- lookupVar v
        case mb of
            Nothing -> return t0
            Just t  -> do
                finalTerm <- fullprune t
                v `bindVar` finalTerm
                return finalTerm


-- BUG: this assumes there are no directly-cyclic chains!
--
-- | Canonicalize a chain of variables so they all point directly
-- to the last variable in the chain, regardless of whether it is
-- bound or not. This allows detecting many cases where multiple
-- variables point to the same term, thereby allowing us to avoid
-- re-unifying the term they point to.
semiprune :: (BindingMonad v t m) => MutTerm v t -> m (MutTerm v t)
semiprune =
    \t0 ->
        case t0 of
        MutTerm _  -> return t0
        MutVar  v0 -> loop t0 v0
    where
    -- We pass the @t@ for @v@ in order to add just a little more sharing.
    loop t v = do
        mb <- lookupVar v
        case mb of
            Nothing -> return t
            Just t' -> 
                case t' of
                MutTerm _  -> return t
                MutVar  v' -> do
                    finalVar <- loop t' v'
                    v `bindVar` finalVar
                    return finalVar


-- | Determine if a variable appears free somewhere inside a term.
-- Since occurs checks only make sense when we're about to bind the
-- variable to the term, we do not bother checking for the possibility
-- of the variable occuring bound in the term.
occursIn :: (BindingMonad v t m) => v (MutTerm v t) -> MutTerm v t -> m Bool
occursIn v t0 = do
    t <- fullprune t0
    case t of
        MutTerm t' -> or <$> mapM (v `occursIn`) t' -- TODO: use foldlM instead
        MutVar  v' -> return $! v `eqVar` v'


-- TODO: use IM.insertWith or the like to do this in one pass
-- | Update the visited-set with a seclaration that a variable has
-- been seen with a given binding, or throw 'OccursIn' if the
-- variable has already been seen.
seenAs
    ::  ( BindingMonad v t m
        , MonadTrans e
        , MonadError (UnificationFailure v t) (e m)
        )
    => v (MutTerm v t) -- ^
    -> MutTerm v t     -- ^
    -> StateT (IM.IntMap (MutTerm v t)) (e m) ()
seenAs v t = do
    seenVars <- get
    case IM.lookup (getVarID v) seenVars of
        Just t' -> lift . throwError $ OccursIn v t'
        Nothing -> put $! IM.insert (getVarID v) t seenVars
{-# INLINE seenAs #-}

----------------------------------------------------------------
----------------------------------------------------------------

-- TODO: these assume pure variables, hence the spine cloning; but
-- we may want to make variants for impure variables with explicit
-- rollback on backtracking.

-- TODO: See if MTL still has that overhead over doing things manually.

-- TODO: Figure out how to abstract the left-catamorphism from these.


-- | Walk a term and determine what variables are still free. N.B.,
-- this function does not detect cyclic terms (i.e., throw errors),
-- but it will return the correct answer for them in finite time.
getFreeVars :: (BindingMonad v t m) => MutTerm v t -> m [v (MutTerm v t)]
getFreeVars =
    \t -> IM.elems <$> evalStateT (loop t) IS.empty
    where
    loop t0 = do
        t1 <- lift $ semiprune t0
        case t1 of
            MutTerm t -> fold <$> mapM loop t -- TODO: use foldlM instead?
            MutVar  v -> do
                seenVars <- get
                let i = getVarID v
                if IS.member i seenVars
                    then return IM.empty -- no (more) free vars down here
                    else do
                        put $! IS.insert i seenVars
                        mb <- lift $ lookupVar v
                        case mb of
                            Just t' -> loop t'
                            Nothing -> return $ IM.singleton i v


-- | Apply the current bindings from the monad so that any remaining
-- variables in the result must, therefore, be free. N.B., this
-- expensively clones term structure and should only be performed
-- when a pure term is needed, or when 'OccursIn' exceptions must
-- be forced. This function /does/ preserve sharing, however that
-- sharing is no longer observed by the monad.
--
-- If any cyclic bindings are detected, then an 'OccursIn' exception
-- will be thrown.
applyBindings
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
applyBindings =
    \t -> evalStateT (loop t) IM.empty
    where
    loop t0 = do
        t1 <- lift . lift $ semiprune t0
        case t1 of
            MutTerm t -> MutTerm <$> mapM loop t
            MutVar  v -> do
                let i = getVarID v
                mb <- IM.lookup i <$> get
                case mb of
                    Just (Right t) -> return t
                    Just (Left  t) -> lift . throwError $ OccursIn v t
                    Nothing -> do
                        mb' <- lift . lift $ lookupVar v
                        case mb' of
                            Nothing -> return t1
                            Just t  -> do
                                modify' . IM.insert i $ Left t
                                t' <- loop t
                                modify' . IM.insert i $ Right t'
                                return t'


-- | Freshen all variables in a term, both bound and free. This
-- ensures that the observability of sharing is maintained, while
-- freshening the free variables. N.B., this expensively clones
-- term structure and should only be performed when necessary.
--
-- If any cyclic bindings are detected, then an 'OccursIn' exception
-- will be thrown.
freshen
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
freshen =
    \t -> evalStateT (loop t) IM.empty
    where
    loop t0 = do
        t1 <- lift . lift $ semiprune t0
        case t1 of
            MutTerm t -> MutTerm <$> mapM loop t
            MutVar  v -> do
                let i = getVarID v
                seenVars <- get
                case IM.lookup i seenVars of
                    Just (Right t) -> return t
                    Just (Left  t) -> lift . throwError $ OccursIn v t
                    Nothing -> do
                        mb <- lift . lift $ lookupVar v
                        case mb of
                            Nothing -> do
                                v' <- lift . lift $ MutVar <$> freeVar
                                put $! IM.insert i (Right v') seenVars
                                return v'
                            Just t  -> do
                                put $! IM.insert i (Left t) seenVars
                                t' <- loop t
                                v' <- lift . lift $ MutVar <$> newVar t'
                                modify' $ IM.insert i (Right v')
                                return v'

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: have to give the signatures for Haddock :(

-- | 'equals'
(===)
    :: (BindingMonad v t m)
    => MutTerm v t  -- ^
    -> MutTerm v t  -- ^
    -> m Bool       -- ^
(===) = equals
infix 4 ===, `equals`


-- | 'equiv'
(=~=)
    :: (BindingMonad v t m)
    => MutTerm v t               -- ^
    -> MutTerm v t               -- ^
    -> m (Maybe (IM.IntMap Int)) -- ^
(=~=) = equiv
infix 4 =~=, `equiv`


-- | 'unify'
(=:=)
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
(=:=) = unify
infix 4 =:=, `unify`


-- | 'subsumes'
(<:=)
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t -- ^
    -> MutTerm v t -- ^
    -> e m Bool
(<:=) = subsumes
infix 4 <:=, `subsumes`

----------------------------------------------------------------

-- TODO: should we offer a variant which gives the reason for failure?
--
-- | Determine if two terms are structurally equal. This is essentially
-- equivalent to @('==')@ except that it does not require applying
-- bindings before comparing, so it is more efficient. N.B., this
-- function does not consider alpha-variance, and thus variables
-- with different names are considered unequal. Cf., 'equiv'.
equals
    :: (BindingMonad v t m)
    => MutTerm v t  -- ^
    -> MutTerm v t  -- ^
    -> m Bool       -- ^
equals =
    \tl tr -> do
        mb <- runMaybeKT (loop tl tr)
        case mb of
            Nothing -> return False
            Just () -> return True
    where
    loop tl0 tr0 = do
        tl <- lift $ semiprune tl0
        tr <- lift $ semiprune tr0
        case (tl, tr) of
            (MutVar vl', MutVar vr')
                | vl' `eqVar` vr' -> return () -- success
                | otherwise       -> do
                    mtl <- lift $ lookupVar vl'
                    mtr <- lift $ lookupVar vr'
                    case (mtl, mtr) of
                        (Nothing,  Nothing ) -> mzero
                        (Nothing,  Just _  ) -> mzero
                        (Just _,   Nothing ) -> mzero
                        (Just tl', Just tr') -> loop tl' tr' -- TODO: should just jump to match
            (MutVar  _,   MutTerm _  ) -> mzero
            (MutTerm _,   MutVar  _  ) -> mzero
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> mzero
                Just tlr -> mapM_ (uncurry loop) tlr


-- TODO: is that the most helpful return type?
--
-- | Determine if two terms are structurally equivalent; that is,
-- structurally equal modulo renaming of free variables. Returns a
-- mapping from variable IDs of the left term to variable IDs of
-- the right term, indicating the renaming used.
equiv
    :: (BindingMonad v t m)
    => MutTerm v t               -- ^
    -> MutTerm v t               -- ^
    -> m (Maybe (IM.IntMap Int)) -- ^
equiv =
    \tl tr -> runMaybeKT (execStateT (loop tl tr) IM.empty)
    where
    loop tl0 tr0 = do
        tl <- lift . lift $ fullprune tl0
        tr <- lift . lift $ fullprune tr0
        case (tl, tr) of
            (MutVar vl',  MutVar  vr') -> do
                let il = getVarID vl'
                let ir = getVarID vr'
                xs <- get
                case IM.lookup il xs of
                    Just x
                        | x == ir   -> return ()
                        | otherwise -> lift mzero
                    Nothing         -> put $! IM.insert il ir xs
            
            (MutVar _,    MutTerm _  ) -> lift mzero
            (MutTerm _,   MutVar  _  ) -> lift mzero
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> lift mzero
                Just tlr -> mapM_ (uncurry loop) tlr


----------------------------------------------------------------
-- Not quite unify2 from the benchmarks, since we do AOOS.
--
-- | A variant of 'unify' which uses 'occursIn' instead of visited-sets.
-- This should only be used when eager throwing of 'OccursIn' errors
-- is absolutely essential (or for testing the correctness of
-- @unify@). Performing the occurs-check is expensive. Not only is
-- it slow, it's asymptotically slow since it can cause the same
-- subterm to be traversed multiple times.
unifyOccurs
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
unifyOccurs = loop
    where
    {-# INLINE (=:) #-}
    v =: t = lift $ v `bindVar` t
    
    {-# INLINE acyclicBindVar #-}
    acyclicBindVar v t = do
        b <- lift $ v `occursIn` t
        if b
            then throwError $ OccursIn v t
            else v =: t
    
    -- TODO: cf todos in 'unify'
    loop tl0 tr0 = do
        tl <- lift $ semiprune tl0
        tr <- lift $ semiprune tr0
        case (tl, tr) of
            (MutVar vl', MutVar vr')
                | vl' `eqVar` vr' -> return tr
                | otherwise       -> do
                    mtl <- lift $ lookupVar vl'
                    mtr <- lift $ lookupVar vr'
                    case (mtl, mtr) of
                        (Nothing,  Nothing ) -> do
                            vl' =: tr
                            return tr
                        (Nothing,  Just _  ) -> do
                            vl' `acyclicBindVar` tr
                            return tr
                        (Just _  , Nothing ) -> do
                            vr' `acyclicBindVar` tl
                            return tl
                        (Just tl', Just tr') -> do
                            t <- loop tl' tr'
                            vr' =: t
                            vl' =: tr
                            return tr
            
            (MutVar vl', MutTerm _) -> do
                mtl <- lift $ lookupVar vl'
                case mtl of
                    Nothing  -> do
                        vl' `acyclicBindVar` tr
                        return tl
                    Just tl' -> do
                        t <- loop tl' tr
                        vl' =: t
                        return tl
            
            (MutTerm _, MutVar vr') -> do
                mtr <- lift $ lookupVar vr'
                case mtr of
                    Nothing  -> do
                        vr' `acyclicBindVar` tl
                        return tr
                    Just tr' -> do
                        t <- loop tl tr'
                        vr' =: t
                        return tr
            
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> throwError $ TermMismatch tl' tr'
                Just tlr -> MutTerm <$> mapM (uncurry loop) tlr


----------------------------------------------------------------
-- TODO: verify correctness, especially for the visited-set stuff.
-- TODO: return Maybe(MutTerm v t) in the loop so we can avoid updating bindings trivially
-- TODO: figure out why unifyOccurs is so much faster on pure ground terms!! The only difference there is in lifting over StateT...
-- 
-- | Unify two terms, or throw an error with an explanation of why
-- unification failed. Since bindings are stored in the monad, the
-- two input terms and the output term are all equivalent if
-- unification succeeds. However, the returned value makes use of
-- aggressive opportunistic observable sharing, so it will be more
-- efficient to use it in future calculations than either argument.
unify
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
unify =
    \tl tr -> evalStateT (loop tl tr) IM.empty
    where
    {-# INLINE (=:) #-}
    v =: t = lift . lift $ v `bindVar` t
    
    -- TODO: would it be beneficial to manually fuse @x <- lift m; y <- lift n@ to @(x,y) <- lift (m;n)@ everywhere we can?
    loop tl0 tr0 = do
        tl <- lift . lift $ semiprune tl0
        tr <- lift . lift $ semiprune tr0
        case (tl, tr) of
            (MutVar vl', MutVar vr')
                | vl' `eqVar` vr' -> return tr
                | otherwise       -> do
                    mtl <- lift . lift $ lookupVar vl'
                    mtr <- lift . lift $ lookupVar vr'
                    case (mtl, mtr) of
                        (Nothing,  Nothing ) -> do vl' =: tr ; return tr
                        (Nothing,  Just _  ) -> do vl' =: tr ; return tr
                        (Just _  , Nothing ) -> do vr' =: tl ; return tl
                        (Just tl', Just tr') -> do
                            t <- localState $ do
                                vl' `seenAs` tl'
                                vr' `seenAs` tr'
                                loop tl' tr' -- TODO: should just jump to match
                            vr' =: t
                            vl' =: tr
                            return tr
            
            (MutVar vl', MutTerm _) -> do
                t <- do
                    mtl <- lift . lift $ lookupVar vl'
                    case mtl of
                        Nothing  -> return tr
                        Just tl' -> localState $ do
                            vl' `seenAs` tl'
                            loop tl' tr -- TODO: should just jump to match
                vl' =: t
                return tl
            
            (MutTerm _, MutVar vr') -> do
                t <- do
                    mtr <- lift . lift $ lookupVar vr'
                    case mtr of
                        Nothing  -> return tl
                        Just tr' -> localState $ do
                            vr' `seenAs` tr'
                            loop tl tr' -- TODO: should just jump to match
                vr' =: t
                return tr
            
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> lift . throwError $ TermMismatch tl' tr'
                Just tlr -> MutTerm <$> mapM (uncurry loop) tlr

----------------------------------------------------------------
-- TODO: can we find an efficient way to return the bindings directly instead of altering the monadic bindings? Maybe another StateT IntMap taking getVarID to the variable and its pseudo-bound term?
--
-- TODO: verify correctness
-- TODO: redo with some codensity
-- TODO: there should be some way to catch OccursIn errors and repair the bindings...

-- | Determine whether the left term subsumes the right term. That
-- is, whereas @(tl =:= tr)@ will compute the most general substitution
-- @s@ such that @(s tl === s tr)@, @(tl <:= tr)@ computes the most
-- general substitution @s@ such that @(s tl === tr)@. This means
-- that @tl@ is less defined than and consistent with @tr@.
--
-- /N.B./, this function updates the monadic bindings just like
-- 'unify' does. However, while the use cases for unification often
-- want to keep the bindings around, the use cases for subsumption
-- usually do not. Thus, you'll probably want to use a binding monad
-- which supports backtracking in order to undo the changes.
-- Unfortunately, leaving the monadic bindings unaltered and returning
-- the necessary substitution directly imposes a performance penalty
-- or else requires specifying too much about the implementation
-- of variables.
subsumes
    ::  ( BindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t -- ^
    -> MutTerm v t -- ^
    -> e m Bool
subsumes =
    \tl tr -> evalStateT (loop tl tr) IM.empty
    where
    {-# INLINE (=:) #-}
    v =: t = lift . lift $ do v `bindVar` t ; return True
    
    -- TODO: cf todos in 'unify'
    loop tl0 tr0 = do
        tl <- lift . lift $ semiprune tl0
        tr <- lift . lift $ semiprune tr0
        case (tl, tr) of
            (MutVar vl', MutVar vr')
                | vl' `eqVar` vr' -> return True
                | otherwise       -> do
                    mtl <- lift . lift $ lookupVar vl'
                    mtr <- lift . lift $ lookupVar vr'
                    case (mtl, mtr) of
                        (Nothing,  Nothing ) -> vl' =: tr
                        (Nothing,  Just _  ) -> vl' =: tr
                        (Just _  , Nothing ) -> return False
                        (Just tl', Just tr') ->
                            localState $ do
                                vl' `seenAs` tl'
                                vr' `seenAs` tr'
                                loop tl' tr'
            
            (MutVar vl',  MutTerm _  ) -> do
                mtl <- lift . lift $ lookupVar vl'
                case mtl of
                    Nothing  -> vl' =: tr
                    Just tl' -> localState $ do
                        vl' `seenAs` tl'
                        loop tl' tr
            
            (MutTerm _,   MutVar  _  ) -> return False
            
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> return False
                Just tlr -> and <$> mapM (uncurry loop) tlr
    

----------------------------------------------------------------
----------------------------------------------------------- fin.
