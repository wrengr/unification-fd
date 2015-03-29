{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-name-shadowing #-}
----------------------------------------------------------------
--                                                  ~ 2015.03.29
-- |
-- Module      :  Control.Unification.Ranked
-- Copyright   :  Copyright (c) 2007--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  highly experimental
-- Portability :  semi-portable (CPP, MPTCs, FlexibleContexts)
--
-- This module provides the API of "Control.Unification" except
-- using 'RankedBindingMonad' where appropriate. This module (and
-- the binding implementations for it) are highly experimental and
-- subject to change in future versions.
----------------------------------------------------------------
module Control.Unification.Ranked
    (
    -- * Data types, classes, etc
      module Control.Unification.Types
    
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
    -- (<:=)
    -- ** Textual names
    , equals
    , equiv
    , unify
    -- unifyOccurs
    -- subsumes
    
    -- * Operations on many terms
    , getFreeVarsAll
    , applyBindingsAll
    , freshenAll
    -- subsumesAll
    ) where

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, or)

import qualified Data.IntMap as IM
import Data.Traversable
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad.Trans  (MonadTrans(..))
#if (MIN_VERSION_mtl(2,2,1))
-- aka: transformers(0,4,1)
import Control.Monad.Except (MonadError(..))
#else
import Control.Monad.Error  (MonadError(..))
#endif
import Control.Monad.State  (MonadState(..), StateT, evalStateT)
import Control.Monad.State.UnificationExtras
import Control.Unification.Types
import Control.Unification hiding (unify, (=:=))
----------------------------------------------------------------
----------------------------------------------------------------

-- | 'unify'
(=:=)
    ::  ( RankedBindingMonad t v m
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


-- HACK: apparently this wasn't exported from Control.Unification; so c&p
-- TODO: use IM.insertWith or the like to do this in one pass
--
-- | Update the visited-set with a seclaration that a variable has
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


-- TODO: keep in sync as we verify correctness.
--
-- | Unify two terms, or throw an error with an explanation of why
-- unification failed. Since bindings are stored in the monad, the
-- two input terms and the output term are all equivalent if
-- unification succeeds. However, the returned value makes use of
-- aggressive opportunistic observable sharing, so it will be more
-- efficient to use it in future calculations than either argument.
unify
    ::  ( RankedBindingMonad t v m
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
    v =: t = bindVar v t >> return t
    
    loop tl0 tr0 = do
        tl0 <- lift . lift $ semiprune tl0
        tr0 <- lift . lift $ semiprune tr0
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return tr0
                | otherwise -> do
                    Rank rl mtl <- lift . lift $ lookupRankVar vl
                    Rank rr mtr <- lift . lift $ lookupRankVar vr
                    let cmp = compare rl rr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> lift . lift $
                            case cmp of
                            LT -> do {                    vl =: tr0 }
                            EQ -> do { incrementRank vr ; vl =: tr0 }
                            GT -> do {                    vr =: tl0 }
                      
                        (Nothing, Just tr) -> lift . lift $
                            case cmp of
                            LT -> do {                    vl =: tr0 }
                            EQ -> do { incrementRank vr ; vl =: tr0 }
                            GT -> do { vl `bindVar` tr  ; vr =: tl0 }
                        
                        (Just tl, Nothing) -> lift . lift $
                            case cmp of
                            LT -> do { vr `bindVar` tl  ; vl =: tr0 }
                            EQ -> do { incrementRank vl ; vr =: tl0 }
                            GT -> do {                    vr =: tl0 }
                        
                        (Just (UTerm tl), Just (UTerm tr)) -> do
                            t <- localState $ do
                                vl `seenAs` tl
                                vr `seenAs` tr
                                match tl tr
                            lift . lift $
                                case cmp of
                                LT -> do { vr `bindVar` t        ; vl =: tr0 }
                                EQ -> do { incrementBindVar vl t ; vr =: tl0 }
                                GT -> do { vl `bindVar` t        ; vr =: tl0 }
                        _ -> error _impossible_unify
            
            (UVar vl, UTerm tr) -> do
                t <- do
                    mtl <- lift . lift $ lookupVar vl
                    case mtl of
                        Nothing -> return tr0
                        Just (UTerm tl) -> localState $ do
                            vl `seenAs` tl
                            match tl tr
                        _ -> error _impossible_unify
                lift . lift $ do
                    vl `bindVar` t
                    return tl0
            
            (UTerm tl, UVar vr) -> do
                t <- do
                    mtr <- lift . lift $ lookupVar vr
                    case mtr of
                        Nothing -> return tl0
                        Just (UTerm tr) -> localState $ do
                            vr `seenAs` tr
                            match tl tr
                        _ -> error _impossible_unify
                lift . lift $ do
                    vr `bindVar` t
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
----------------------------------------------------------- fin.
