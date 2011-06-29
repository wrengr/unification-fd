
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.06.28
-- |
-- Module      :  Control.Monad.State.UnificationExtras
-- Copyright   :  Copyright (c) 2008--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  unstable
-- Portability :  semi-portable (MPTCs)
--
-- This module defines some extra functions for "Control.Monad.State.Lazy".
--
-- TODO: patch transformers\/mtl-2 with these functions.
----------------------------------------------------------------
module Control.Monad.State.UnificationExtras
    (
    -- * Additional functions for MTL
      liftReader
    , liftReaderT
    , modify'
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

----------------------------------------------------------------
----------------------------------------------------------- fin.
