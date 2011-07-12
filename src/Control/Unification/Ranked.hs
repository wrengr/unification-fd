
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.11
-- |
-- Module      :  Control.Unification.Ranked
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  highly experimental
-- Portability :  semi-portable (MPTCs, FlexibleContexts)
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
    ) where

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, or)

import qualified Data.IntMap as IM
import Data.Traversable
import Control.Applicative
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Error (MonadError(..))
import Control.Monad.State (MonadState(..), evalStateT)
import Control.Monad.State.UnificationExtras
import Control.Unification.Types
import Control.Unification hiding (unify, (=:=))
----------------------------------------------------------------
----------------------------------------------------------------

-- | 'unify'
(=:=)
    ::  ( RankedBindingMonad v t m
        , MonadTrans e
        , Functor (e m) -- Grr, Monad(e m) should imply Functor(e m)
        , MonadError (UnificationFailure v t) (e m)
        )
    => MutTerm v t       -- ^
    -> MutTerm v t       -- ^
    -> e m (MutTerm v t) -- ^
(=:=) = unify
infix 4 =:=, `unify`


-- TODO: keep in sync as we verify correctness.
--
-- | Unify two terms, or throw an error with an explanation of why
-- unification failed. Since bindings are stored in the monad, the
-- two input terms and the output term are all equivalent if
-- unification succeeds. However, the returned value makes use of
-- aggressive opportunistic observable sharing, so it will be more
-- efficient to use it in future calculations than either argument.
unify
    ::  ( RankedBindingMonad v t m
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
    -- TODO: use IM.insertWith or the like to do this in one pass
    {-# INLINE seenAs #-}
    v `seenAs` t = do
        seenVars <- get
        case IM.lookup (getVarID v) seenVars of
            Just t' -> lift . throwError $ OccursIn v t'
            Nothing -> put $ IM.insert (getVarID v) t seenVars
    
    {-# INLINE (=:) #-}
    v =: t = bindVar v t >> return t
    
    loop tl0 tr0 = do
        tl1 <- lift . lift $ semiprune tl0
        tr1 <- lift . lift $ semiprune tr0
        case (tl1, tr1) of
            (MutVar vl, MutVar vr)
                | vl `eqVar` vr -> return tr1
                | otherwise     -> do
                    Rank rl mtl <- lift . lift $ lookupRankVar vl
                    Rank rr mtr <- lift . lift $ lookupRankVar vr
                    let cmp = compare rl rr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> lift . lift $
                            case cmp of
                            LT -> do {                    vl =: tr1 }
                            EQ -> do { incrementRank vr ; vl =: tr1 }
                            GT -> do {                    vr =: tl1 }
                      
                        (Nothing, Just tr) -> lift . lift $
                            case cmp of
                            LT -> do {                    vl =: tr1 }
                            EQ -> do { incrementRank vr ; vl =: tr1 }
                            GT -> do { vl `bindVar` tr  ; vr =: tl1 }
                        
                        (Just tl, Nothing) -> lift . lift $
                            case cmp of
                            LT -> do { vr `bindVar` tl  ; vl =: tr1 }
                            EQ -> do { incrementRank vl ; vr =: tl1 }
                            GT -> do {                    vr =: tl1 }
                        
                        (Just tl, Just tr) -> do
                            t <- localState $ do
                                vl `seenAs` tl
                                vr `seenAs` tr
                                loop tl tr
                            lift . lift $
                                case cmp of
                                LT -> do { vr `bindVar` t        ; vl =: tr1 }
                                EQ -> do { incrementBindVar vl t ; vr =: tl1 }
                                GT -> do { vl `bindVar` t        ; vr =: tl1 }
            
            (MutVar vl, MutTerm _) -> do
                t <- do
                    mtl <- lift . lift $ lookupVar vl
                    case mtl of
                        Nothing -> return tr1
                        Just tl -> localState $ do
                            vl `seenAs` tl
                            loop tl tr1
                lift . lift $ do
                    vl `bindVar` t
                    return tl1
            
            (MutTerm _, MutVar vr) -> do
                t <- do
                    mtr <- lift . lift $ lookupVar vr
                    case mtr of
                        Nothing -> return tl1
                        Just tr -> localState $ do
                            vr `seenAs` tr
                            loop tl1 tr
                lift . lift $ do
                    vr `bindVar` t
                    return tr1
            
            (MutTerm tl, MutTerm tr) ->
                case zipMatch tl tr of
                Nothing  -> lift . throwError $ TermMismatch tl tr
                Just tlr -> MutTerm <$> mapM (uncurry loop) tlr

----------------------------------------------------------------
----------------------------------------------------------- fin.
