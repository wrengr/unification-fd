{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-name-shadowing #-}

-- HACK: in GHC 7.10, Haddock complains about unused imports; but,
-- if we use CPP to avoid including them under Haddock, then it
-- will fail!
#ifdef __HADDOCK__
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#endif
----------------------------------------------------------------
--                                                  ~ 2015.03.29
-- |
-- Module      :  Control.Unification
-- Copyright   :  Copyright (c) 2007--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (CPP, MPTCs, FlexibleContexts)
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
    -- ** Unification terms
      UTerm(..)
    , freeze
    , unfreeze
    -- ** Errors
    , Fallible(..)
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
    
    -- * Operations on many terms
    , getFreeVarsAll
    , applyBindingsAll
    , freshenAll
    -- subsumesAll -- to ensure that there's a single coherent substitution allowing the schema to subsume all the terms in some collection.

    -- * Helper functions
    -- | Client code should not need to use these functions, but
    -- they are exposed just in case they are needed.
    , fullprune
    , semiprune
    , occursIn
    -- TODO: add a post-hoc occurs check in order to have a version of unify which is fast, yet is also guaranteed to fail when it ought to (rather than deferring the failure until later, as the current unify does).
    ) where

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, and, or)

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Foldable
import Data.Traversable
import Control.Monad.Identity (Identity(..))
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad        (MonadPlus(..))
import Control.Monad.Trans  (MonadTrans(..))
#if (MIN_VERSION_mtl(2,2,1))
-- aka: transformers(0,4,1)
import Control.Monad.Except (MonadError(..))
#else
import Control.Monad.Error  (MonadError(..))
#endif
import Control.Monad.State  (MonadState(..), StateT, evalStateT, execStateT)
import Control.Monad.MaybeK
import Control.Monad.State.UnificationExtras
import Control.Unification.Types
----------------------------------------------------------------
----------------------------------------------------------------

-- N.B., this assumes there are no directly-cyclic chains!
--
-- | Canonicalize a chain of variables so they all point directly
-- to the term at the end of the chain (or the free variable, if
-- the chain is unbound), and return that end.
--
-- N.B., this is almost never the function you want. Cf., 'semiprune'.
fullprune :: (BindingMonad t v m) => UTerm t v -> m (UTerm t v)
fullprune t0@(UTerm _ ) = return t0
fullprune t0@(UVar  v0) = do
    mb <- lookupVar v0
    case mb of
        Nothing -> return t0
        Just t  -> do
            finalTerm <- fullprune t
            v0 `bindVar` finalTerm
            return finalTerm


-- N.B., this assumes there are no directly-cyclic chains!
--
-- | Canonicalize a chain of variables so they all point directly
-- to the last variable in the chain, regardless of whether it is
-- bound or not. This allows detecting many cases where multiple
-- variables point to the same term, thereby allowing us to avoid
-- re-unifying the term they point to.
semiprune :: (BindingMonad t v m) => UTerm t v -> m (UTerm t v)
semiprune t0@(UTerm _ ) = return t0
semiprune t0@(UVar  v0) = loop t0 v0
    where
    -- We pass the @t@ for @v@ in order to add just a little more sharing.
    loop t0 v0 = do
        mb <- lookupVar v0
        case mb of
            Nothing -> return t0
            Just t  ->
                case t  of
                UTerm _  -> return t0
                UVar  v  -> do
                    finalVar <- loop t v
                    v0 `bindVar` finalVar
                    return finalVar


-- | Determine if a variable appears free somewhere inside a term.
-- Since occurs checks only make sense when we're about to bind the
-- variable to the term, we do not bother checking for the possibility
-- of the variable occuring bound in the term.
occursIn :: (BindingMonad t v m) => v -> UTerm t v -> m Bool
{-# INLINE occursIn #-}
occursIn v0 t0 = do
    t0 <- fullprune t0
    case t0 of
        UTerm t -> or <$> mapM (v0 `occursIn`) t
            -- TODO: benchmark the following for shortcircuiting
            -- > Traversable.foldlM (\b t' -> if b then return True else v0 `occursIn` t') t
        UVar  v -> return $! v0 == v


-- TODO: what was the reason for the MonadTrans madness?
-- TODO: use IM.insertWith or the like to do this in one pass
--
-- | Update the visited-set with a declaration that a variable has
-- been seen with a given binding, or throw 'occursFailure' if the
-- variable has already been seen.
seenAs
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , MonadError e (em m)
        )
    => v -- ^
    -> t (UTerm t v) -- ^
    -> StateT (IM.IntMap (t (UTerm t v))) (em m) () -- ^
{-# INLINE seenAs #-}
seenAs v0 t0 = do
    seenVars <- get
    case IM.lookup (getVarID v0) seenVars of
        Just t  -> lift . throwError $ occursFailure v0 (UTerm t)
        Nothing -> put $! IM.insert (getVarID v0) t0 seenVars

----------------------------------------------------------------
----------------------------------------------------------------

-- TODO: these assume pure variables, hence the spine cloning; but
-- we may want to make variants for impure variables with explicit
-- rollback on backtracking.

-- TODO: See if MTL still has that overhead over doing things manually.

-- TODO: Figure out how to abstract the left-catamorphism from these.


-- | Walk a term and determine which variables are still free. N.B.,
-- this function does not detect cyclic terms (i.e., throw errors),
-- but it will return the correct answer for them in finite time.
getFreeVars :: (BindingMonad t v m) => UTerm t v -> m [v]
getFreeVars = getFreeVarsAll . Identity


-- TODO: Should we return the IntMap instead?
--
-- | Same as 'getFreeVars', but works on several terms simultaneously.
-- This is more efficient than getting the free variables for each
-- of the terms separately because we can make use of sharing across
-- the whole collection. That is, each time we move to the next
-- term, we still remember the bound variables we've already looked
-- at (and therefore do not need to traverse, since we've already
-- seen whatever free variables there are down there); whereas we
-- would forget between each call to @getFreeVars@.
--
-- /Since: 0.7.0/
getFreeVarsAll
    :: (BindingMonad t v m, Foldable s)
    => s (UTerm t v) -> m [v]
getFreeVarsAll ts0 =
    IM.elems <$> evalStateT (loopAll ts0) IS.empty
    where
    -- TODO: is that the most efficient direction/associativity?
    loopAll = foldrM (\t r -> IM.union r <$> loop t) IM.empty

    loop t0 = do
        t0 <- lift $ semiprune t0
        case t0 of
            UTerm t -> fold <$> mapM loop t
                -- TODO: benchmark using the following instead:
                -- > foldMapM f = foldlM (\a b -> mappend a <$> f b) mempty
            UVar  v -> do
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


-- TODO: what was the reason for the MonadTrans madness?
--
-- | Apply the current bindings from the monad so that any remaining
-- variables in the result must, therefore, be free. N.B., this
-- expensively clones term structure and should only be performed
-- when a pure term is needed, or when 'occursFailure' exceptions
-- must be forced. This function /does/ preserve sharing, however
-- that sharing is no longer observed by the monad.
--
-- If any cyclic bindings are detected, then an 'occursFailure'
-- exception will be thrown.
applyBindings
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v       -- ^
    -> em m (UTerm t v) -- ^
applyBindings = fmap runIdentity . applyBindingsAll . Identity


-- TODO: what was the reason for the MonadTrans madness?
--
-- | Same as 'applyBindings', but works on several terms simultaneously.
-- This function preserves sharing across the entire collection of
-- terms, whereas applying the bindings to each term separately
-- would only preserve sharing within each term.
--
-- /Since: 0.7.0/
applyBindingsAll
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        , Traversable s
        )
    => s (UTerm t v)        -- ^
    -> em m (s (UTerm t v)) -- ^
applyBindingsAll ts0 = evalStateT (mapM loop ts0) IM.empty
    where
    loop t0 = do
        t0 <- lift . lift $ semiprune t0
        case t0 of
            UTerm t -> UTerm <$> mapM loop t
            UVar  v -> do
                let i = getVarID v
                mb <- IM.lookup i <$> get
                case mb of
                    Just (Right t) -> return t
                    Just (Left  t) -> lift . throwError $ occursFailure v t
                    Nothing -> do
                        mb' <- lift . lift $ lookupVar v
                        case mb' of
                            Nothing -> return t0
                            Just t  -> do
                                modify' . IM.insert i $ Left t
                                t' <- loop t
                                modify' . IM.insert i $ Right t'
                                return t'


-- TODO: what was the reason for the MonadTrans madness?
--
-- | Freshen all variables in a term, both bound and free. This
-- ensures that the observability of sharing is maintained, while
-- freshening the free variables. N.B., this expensively clones
-- term structure and should only be performed when necessary.
--
-- If any cyclic bindings are detected, then an 'occursFailure'
-- exception will be thrown.
freshen
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v       -- ^
    -> em m (UTerm t v) -- ^
freshen = fmap runIdentity . freshenAll . Identity


-- TODO: what was the reason for the MonadTrans madness?
--
-- | Same as 'freshen', but works on several terms simultaneously.
-- This is different from freshening each term separately, because
-- @freshenAll@ preserves the relationship between the terms. For
-- instance, the result of
--
-- > mapM freshen [UVar 1, UVar 1]
--
-- would be @[UVar 2, UVar 3]@ or something alpha-equivalent, whereas
-- the result of
--
-- > freshenAll [UVar 1, UVar 1]
--
-- would be @[UVar 2, UVar 2]@ or something alpha-equivalent.
--
-- /Since: 0.7.0/
freshenAll
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        , Traversable s
        )
    => s (UTerm t v)        -- ^
    -> em m (s (UTerm t v)) -- ^
freshenAll ts0 = evalStateT (mapM loop ts0) IM.empty
    where
    loop t0 = do
        t0 <- lift . lift $ semiprune t0
        case t0 of
            UTerm t -> UTerm <$> mapM loop t
            UVar  v -> do
                let i = getVarID v
                seenVars <- get
                case IM.lookup i seenVars of
                    Just (Right t) -> return t
                    Just (Left  t) -> lift . throwError $ occursFailure v t
                    Nothing -> do
                        mb <- lift . lift $ lookupVar v
                        case mb of
                            Nothing -> do
                                v' <- lift . lift $ UVar <$> freeVar
                                put $! IM.insert i (Right v') seenVars
                                return v'
                            Just t  -> do
                                put $! IM.insert i (Left t) seenVars
                                t' <- loop t
                                v' <- lift . lift $ UVar <$> newVar t'
                                modify' $ IM.insert i (Right v')
                                return v'

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: have to give the signatures for Haddock :(

-- | 'equals'
(===)
    :: (BindingMonad t v m)
    => UTerm t v  -- ^
    -> UTerm t v  -- ^
    -> m Bool     -- ^
(===) = equals
{-# INLINE (===) #-}
infix 4 ===, `equals`


-- | 'equiv'
(=~=)
    :: (BindingMonad t v m)
    => UTerm t v                 -- ^
    -> UTerm t v                 -- ^
    -> m (Maybe (IM.IntMap Int)) -- ^
(=~=) = equiv
{-# INLINE (=~=) #-}
infix 4 =~=, `equiv`


-- TODO: what was the reason for the MonadTrans madness?
-- | 'unify'
(=:=)
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v        -- ^
    -> UTerm t v        -- ^
    -> em m (UTerm t v) -- ^
(=:=) = unify
{-# INLINE (=:=) #-}
infix 4 =:=, `unify`


-- TODO: what was the reason for the MonadTrans madness?
-- | 'subsumes'
(<:=)
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v -- ^
    -> UTerm t v -- ^
    -> em m Bool -- ^
(<:=) = subsumes
{-# INLINE (<:=) #-}
infix 4 <:=, `subsumes`

----------------------------------------------------------------

{- BUG:
If we don't use anything special, then there's a 2x overhead for
calling 'equals' (and probably the rest of them too). If we add a
SPECIALIZE pragma, or if we try to use MaybeT instead of MaybeKT
then that jumps up to 4x overhead. However, if we add an INLINE
pragma then it gets faster than the same implementation in the
benchmark file. I've no idea what's going on here...
-}

-- TODO: should we offer a variant which gives the reason for failure?
--
-- | Determine if two terms are structurally equal. This is essentially
-- equivalent to @('==')@ except that it does not require applying
-- bindings before comparing, so it is more efficient. N.B., this
-- function does not consider alpha-variance, and thus variables
-- with different names are considered unequal. Cf., 'equiv'.
equals
    :: (BindingMonad t v m)
    => UTerm t v  -- ^
    -> UTerm t v  -- ^
    -> m Bool     -- ^
equals tl0 tr0 = do
    mb <- runMaybeKT (loop tl0 tr0)
    case mb of
        Nothing -> return False
        Just () -> return True
    where
    loop tl0 tr0 = do
        tl0 <- lift $ semiprune tl0
        tr0 <- lift $ semiprune tr0
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return () -- success
                | otherwise -> do
                    mtl <- lift $ lookupVar vl
                    mtr <- lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing,         Nothing)         -> mzero
                        (Nothing,         Just _ )         -> mzero
                        (Just _,          Nothing)         -> mzero
                        (Just (UTerm tl), Just (UTerm tr)) -> match tl tr
                        _ -> error _impossible_equals
            (UVar  _,  UTerm _ ) -> mzero
            (UTerm _,  UVar  _ ) -> mzero
            (UTerm tl, UTerm tr) -> match tl tr
    
    match tl tr =
        case zipMatch tl tr of
        Nothing  -> mzero
        Just tlr -> mapM_ loop_ tlr
    
    loop_ (Left  _)       = return () -- success
    loop_ (Right (tl,tr)) = loop tl tr

_impossible_equals :: String
{-# NOINLINE _impossible_equals #-}
_impossible_equals = "equals: the impossible happened"


-- TODO: is that the most helpful return type?
--
-- | Determine if two terms are structurally equivalent; that is,
-- structurally equal modulo renaming of free variables. Returns a
-- mapping from variable IDs of the left term to variable IDs of
-- the right term, indicating the renaming used.
equiv
    :: (BindingMonad t v m)
    => UTerm t v                 -- ^
    -> UTerm t v                 -- ^
    -> m (Maybe (IM.IntMap Int)) -- ^
equiv tl0 tr0 = runMaybeKT (execStateT (loop tl0 tr0) IM.empty)
    where
    loop tl0 tr0 = do
        tl0 <- lift . lift $ fullprune tl0
        tr0 <- lift . lift $ fullprune tr0
        case (tl0, tr0) of
            (UVar vl,  UVar  vr) -> do
                let il = getVarID vl
                let ir = getVarID vr
                xs <- get
                case IM.lookup il xs of
                    Just x
                        | x == ir   -> return () -- success; no changes
                        | otherwise -> lift mzero
                    Nothing         -> put $! IM.insert il ir xs
            
            (UVar  _,  UTerm _ ) -> lift mzero
            (UTerm _,  UVar  _ ) -> lift mzero
            (UTerm tl, UTerm tr) ->
                case zipMatch tl tr of
                Nothing  -> lift mzero
                Just tlr -> mapM_ loop_ tlr
    
    loop_ (Left  _)       = return () -- success; no changes
    loop_ (Right (tl,tr)) = loop tl tr


----------------------------------------------------------------
-- Not quite unify2 from the benchmarks, since we do AOOS.
-- TODO: what was the reason for the MonadTrans madness?
--
-- | A variant of 'unify' which uses 'occursIn' instead of visited-sets.
-- This should only be used when eager throwing of 'occursFailure'
-- errors is absolutely essential (or for testing the correctness
-- of @unify@). Performing the occurs-check is expensive. Not only
-- is it slow, it's asymptotically slow since it can cause the same
-- subterm to be traversed multiple times.
unifyOccurs
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v        -- ^
    -> UTerm t v        -- ^
    -> em m (UTerm t v) -- ^
unifyOccurs = loop
    where
    {-# INLINE (=:) #-}
    v =: t = lift $ v `bindVar` t
    
    {-# INLINE acyclicBindVar #-}
    acyclicBindVar v t = do
        b <- lift $ v `occursIn` t
        if b
            then throwError $ occursFailure v t
            else v =: t
    
    -- TODO: cf todos in 'unify'
    loop tl0 tr0 = do
        tl0 <- lift $ semiprune tl0
        tr0 <- lift $ semiprune tr0
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return tr0
                | otherwise -> do
                    mtl <- lift $ lookupVar vl
                    mtr <- lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> do
                            vl =: tr0
                            return tr0
                        (Nothing, Just _ ) -> do
                            vl `acyclicBindVar` tr0
                            return tr0
                        (Just _ , Nothing) -> do
                            vr `acyclicBindVar` tl0
                            return tl0
                        (Just (UTerm tl), Just (UTerm tr)) -> do
                            t <- match tl tr
                            vr =: t
                            vl =: tr0
                            return tr0
                        _ -> error _impossible_unifyOccurs
            
            (UVar vl, UTerm tr) -> do
                mtl <- lift $ lookupVar vl
                case mtl of
                    Nothing  -> do
                        vl `acyclicBindVar` tr0
                        return tl0
                    Just (UTerm tl) -> do
                        t <- match tl tr
                        vl =: t
                        return tl0
                    _ -> error _impossible_unifyOccurs
            
            (UTerm tl, UVar vr) -> do
                mtr <- lift $ lookupVar vr
                case mtr of
                    Nothing  -> do
                        vr `acyclicBindVar` tl0
                        return tr0
                    Just (UTerm tr) -> do
                        t <- match tl tr
                        vr =: t
                        return tr0
                    _ -> error _impossible_unifyOccurs
            
            (UTerm tl, UTerm tr) -> match tl tr
    
    match tl tr =
        case zipMatch tl tr of
        Nothing  -> throwError $ mismatchFailure tl tr
        Just tlr -> UTerm <$> mapM loop_ tlr
    
    loop_ (Left  t)       = return t
    loop_ (Right (tl,tr)) = loop tl tr

_impossible_unifyOccurs :: String
{-# NOINLINE _impossible_unifyOccurs #-}
_impossible_unifyOccurs = "unifyOccurs: the impossible happened"


----------------------------------------------------------------
-- TODO: verify correctness, especially for the visited-set stuff.
-- TODO: return Maybe(UTerm t v) in the loop so we can avoid updating bindings trivially
-- TODO: figure out why unifyOccurs is so much faster on pure ground terms!! The only difference there is in lifting over StateT...
-- TODO: what was the reason for the MonadTrans madness?
--
-- | Unify two terms, or throw an error with an explanation of why
-- unification failed. Since bindings are stored in the monad, the
-- two input terms and the output term are all equivalent if
-- unification succeeds. However, the returned value makes use of
-- aggressive opportunistic observable sharing, so it will be more
-- efficient to use it in future calculations than either argument.
unify
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v        -- ^
    -> UTerm t v        -- ^
    -> em m (UTerm t v) -- ^
unify tl0 tr0 = evalStateT (loop tl0 tr0) IM.empty
    where
    {-# INLINE (=:) #-}
    v =: t = lift . lift $ v `bindVar` t
    
    -- TODO: would it be beneficial to manually fuse @x <- lift m; y <- lift n@ to @(x,y) <- lift (m;n)@ everywhere we can?
    loop tl0 tr0 = do
        tl0 <- lift . lift $ semiprune tl0
        tr0 <- lift . lift $ semiprune tr0
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return tr0
                | otherwise -> do
                    mtl <- lift . lift $ lookupVar vl
                    mtr <- lift . lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> do vl =: tr0 ; return tr0
                        (Nothing, Just _ ) -> do vl =: tr0 ; return tr0
                        (Just _ , Nothing) -> do vr =: tl0 ; return tl0
                        (Just (UTerm tl), Just (UTerm tr)) -> do
                            t <- localState $ do
                                vl `seenAs` tl
                                vr `seenAs` tr
                                match tl tr
                            vr =: t
                            vl =: tr0
                            return tr0
                        _ -> error _impossible_unify
            
            (UVar vl, UTerm tr) -> do
                t <- do
                    mtl <- lift . lift $ lookupVar vl
                    case mtl of
                        Nothing         -> return tr0
                        Just (UTerm tl) -> localState $ do
                            vl `seenAs` tl
                            match tl tr
                        _ -> error _impossible_unify
                vl =: t
                return tl0
            
            (UTerm tl, UVar vr) -> do
                t <- do
                    mtr <- lift . lift $ lookupVar vr
                    case mtr of
                        Nothing         -> return tl0
                        Just (UTerm tr) -> localState $ do
                            vr `seenAs` tr
                            match tl tr
                        _ -> error _impossible_unify
                vr =: t
                return tr0
            
            (UTerm tl, UTerm tr) -> match tl tr
    
    match tl tr =
        case zipMatch tl tr of
        Nothing  -> lift . throwError $ mismatchFailure tl tr
        Just tlr -> UTerm <$> mapM loop_ tlr
    
    loop_ (Left  t)       = return t
    loop_ (Right (tl,tr)) = loop tl tr

_impossible_unify :: String
{-# NOINLINE _impossible_unify #-}
_impossible_unify = "unify: the impossible happened"

----------------------------------------------------------------
-- TODO: can we find an efficient way to return the bindings directly
-- instead of altering the monadic bindings? Maybe another StateT
-- IntMap taking getVarID to the variable and its pseudo-bound term?
--
-- TODO: verify correctness
-- TODO: redo with some codensity
-- TODO: there should be some way to catch occursFailure errors and repair the bindings...
-- TODO: what was the reason for the MonadTrans madness?

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
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        )
    => UTerm t v -- ^
    -> UTerm t v -- ^
    -> em m Bool -- ^
subsumes tl0 tr0 = evalStateT (loop tl0 tr0) IM.empty
    where
    {-# INLINE (=:) #-}
    v =: t = lift . lift $ do v `bindVar` t ; return True
    
    -- TODO: cf todos in 'unify'
    loop tl0 tr0 = do
        tl0 <- lift . lift $ semiprune tl0
        tr0 <- lift . lift $ semiprune tr0
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return True
                | otherwise -> do
                    mtl <- lift . lift $ lookupVar vl
                    mtr <- lift . lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing,         Nothing)         -> vl =: tr0
                        (Nothing,         Just _ )         -> vl =: tr0
                        (Just _ ,         Nothing)         -> return False
                        (Just (UTerm tl), Just (UTerm tr)) ->
                            localState $ do
                                vl `seenAs` tl
                                vr `seenAs` tr
                                match tl tr
                        _ -> error _impossible_subsumes
            
            (UVar vl,  UTerm tr) -> do
                mtl <- lift . lift $ lookupVar vl
                case mtl of
                    Nothing         -> vl =: tr0
                    Just (UTerm tl) -> localState $ do
                        vl `seenAs` tl
                        match tl tr
                    _ -> error _impossible_subsumes
            
            (UTerm _,  UVar  _ ) -> return False
            
            (UTerm tl, UTerm tr) -> match tl tr
    
    match tl tr =
        case zipMatch tl tr of
        Nothing  -> return False
        Just tlr -> and <$> mapM loop_ tlr -- TODO: use foldlM?
    
    loop_ (Left  _)       = return True
    loop_ (Right (tl,tr)) = loop tl tr

_impossible_subsumes :: String
{-# NOINLINE _impossible_subsumes #-}
_impossible_subsumes = "subsumes: the impossible happened"

----------------------------------------------------------------
----------------------------------------------------------- fin.
