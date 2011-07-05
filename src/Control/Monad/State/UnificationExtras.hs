
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.05
-- |
-- Module      :  Control.Monad.State.UnificationExtras
-- Copyright   :  Copyright (c) 2008--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  perpetually unstable
-- Portability :  semi-portable (MPTCs)
--
-- This module defines some extra functions for "Control.Monad.State.Lazy".
-- This package really isn't the proper place for these, but we
-- need them to be somewhere.
--
-- TODO: patch transformers\/mtl-2 with these functions.
----------------------------------------------------------------
module Control.Monad.State.UnificationExtras
    (
    -- * Additional functions for MTL
      liftReader
    , liftReaderT
    , modify'
    , localState
    ) where

import Control.Monad            (liftM)
import Control.Monad.Reader     (Reader(), ReaderT(..))
import Control.Monad.State.Lazy (MonadState(..), State(), StateT(..))

----------------------------------------------------------------
----------------------------------------------------------------

-- | Lift a reader into a state monad. More particularly, this
-- allows disabling mutability in a local context within @StateT@.
liftReaderT :: (Monad m) => ReaderT e m a -> StateT e m a
liftReaderT r = StateT $ \e -> liftM (\a -> (a,e)) (runReaderT r e)


-- | Lift a reader into a state monad. More particularly, this
-- allows disabling mutability in a local context within @State@.
liftReader :: Reader e a -> State e a
liftReader = liftReaderT


-- | A strict version of 'modify'.
modify' :: (MonadState s m) => (s -> s) -> m ()
modify' f = do
    s <- get
    put $! f s
{-# INLINE modify' #-}


-- | Run a state action and undo the state changes at the end.
localState :: (MonadState s m) => m a -> m a
localState m = do
    s <- get
    x <- m
    put s
    return x
{-# INLINE localState #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
