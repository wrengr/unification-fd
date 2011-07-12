
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.06
-- |
-- Module      :  Control.Unification.IntVar
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (MPTCs,...)
--
-- This module defines a state monad for functional pointers
-- represented by integers as keys into an @IntMap@. This technique
-- was independently discovered by Dijkstra et al. This module
-- extends the approach by using a state monad transformer, which
-- can be made into a backtracking state monad by setting the
-- underlying monad to some 'MonadLogic' (part of the @logict@
-- library, described by Kiselyov et al.).
--
--     * Atze Dijkstra, Arie Middelkoop, S. Doaitse Swierstra (2008)
--         /Efficient Functional Unification and Substitution/,
--         Technical Report UU-CS-2008-027, Utrecht University.
--
--     * Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, and
--         Amr Sabry (2005) /Backtracking, Interleaving, and/
--         /Terminating Monad Transformers/, ICFP.
----------------------------------------------------------------
module Control.Unification.IntVar
    ( IntVar(..)
    , IntBindingState()
    , IntBindingT()
    , runIntBindingT
    , evalIntBindingT
    , execIntBindingT
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)

import qualified Data.IntMap as IM
import Control.Applicative
import Control.Monad         (MonadPlus(..), liftM)
import Control.Monad.Trans   (MonadTrans(..))
import Control.Monad.State   (MonadState(..), StateT, runStateT, evalStateT, execStateT, gets)
import Control.Monad.Logic   (MonadLogic(..))
import Control.Unification.Types
----------------------------------------------------------------
----------------------------------------------------------------

-- | A \"mutable\" unification variable implemented by an integer.
-- This provides an entirely pure alternative to truly mutable
-- alternatives (like @STVar@), which can make backtracking easier.
--
-- N.B., because this implementation is pure, we can use it for
-- both ranked and unranked monads.
newtype IntVar t = IntVar Int
    deriving (Show)

{-
-- BUG: This part works, but we'd want to change Show IntBindingState too.

instance Show (IntVar t) where
    show (IntVar i) = "IntVar " ++ show (boundedInt2Word i)

-- | Convert an integer to a word, via the continuous mapping that
-- preserves @minBound@ and @maxBound@.
boundedInt2Word :: Int -> Word
boundedInt2Word i
    | i < 0     = fromIntegral (i + maxBound + 1)
    | otherwise = fromIntegral i + fromIntegral (maxBound :: Int) + 1
-}

instance Variable IntVar where
    eqVar (IntVar i) (IntVar j) = i == j
    
    getVarID (IntVar v) = v


----------------------------------------------------------------
-- | Binding state for 'IntVar'.
data IntBindingState t = IntBindingState
    { nextFreeVar :: {-# UNPACK #-} !Int
    , varBindings :: IM.IntMap (MutTerm IntVar t)
    }

-- Can't derive this because it's an UndecidableInstance
instance (Show (t (MutTerm IntVar t))) =>
    Show (IntBindingState t)
    where
    show (IntBindingState nr bs) =
        "IntBindingState { nextFreeVar = "++show nr++
        ", varBindings = "++show bs++"}"

-- | The initial @IntBindingState@.
emptyIntBindingState :: IntBindingState t
emptyIntBindingState = IntBindingState minBound IM.empty


----------------------------------------------------------------
-- | A monad for storing 'IntVar' bindings, implemented as a 'StateT'.
-- For a plain state monad, set @m = Identity@; for a backtracking
-- state monad, set @m = Logic@.
newtype IntBindingT t m a = IBT { unIBT :: StateT (IntBindingState t) m a }

-- For portability reasons, we're intentionally avoiding
-- -XDeriveFunctor, -XGeneralizedNewtypeDeriving, and the like.

instance (Functor m) => Functor (IntBindingT t m) where
    fmap f = IBT . fmap f . unIBT

-- BUG: can't reduce dependency to Applicative because of StateT's instance.
instance (Functor m, Monad m) => Applicative (IntBindingT t m) where
    pure    = IBT . pure
    x <*> y = IBT (unIBT x <*> unIBT y)
    x  *> y = IBT (unIBT x  *> unIBT y)
    x <*  y = IBT (unIBT x <*  unIBT y)

instance (Monad m) => Monad (IntBindingT t m) where
    return  = IBT . return
    m >>= f = IBT (unIBT m >>= unIBT . f)

instance MonadTrans (IntBindingT t) where
    lift = IBT . lift

-- BUG: can't reduce dependency to Alternative because of StateT's instance.
instance (Functor m, MonadPlus m) => Alternative (IntBindingT t m) where
    empty   = IBT empty
    x <|> y = IBT (unIBT x <|> unIBT y)

instance (MonadPlus m) => MonadPlus (IntBindingT t m) where
    mzero       = IBT mzero
    mplus ml mr = IBT (mplus (unIBT ml) (unIBT mr))

instance (Monad m) => MonadState (IntBindingState t) (IntBindingT t m) where
    get = IBT get
    put = IBT . put

-- N.B., we already have (MonadLogic m) => MonadLogic (StateT s m),
-- provided that logict is compiled against the same mtl/monads-fd
-- we're getting StateT from. Otherwise we'll get a bunch of warnings
-- here.
instance (MonadLogic m) => MonadLogic (IntBindingT t m) where
    msplit (IBT m) = IBT (coerce `liftM` msplit m)
        where
        coerce Nothing        = Nothing
        coerce (Just (a, m')) = Just (a, IBT m')
    
    interleave (IBT l) (IBT r) = IBT (interleave l r)
    
    IBT m >>- f = IBT (m >>- (unIBT . f))
    
    ifte (IBT b) t (IBT f) = IBT (ifte b (unIBT . t) f)
    
    once (IBT m) = IBT (once m)

----------------------------------------------------------------

runIntBindingT :: IntBindingT t m a -> m (a, IntBindingState t)
runIntBindingT (IBT m) = runStateT m emptyIntBindingState


-- | N.B., you should explicitly apply bindings before calling this
-- function, or else the bindings will be lost
evalIntBindingT :: (Monad m) => IntBindingT t m a -> m a
evalIntBindingT (IBT m) = evalStateT m emptyIntBindingState


execIntBindingT :: (Monad m) => IntBindingT t m a -> m (IntBindingState t)
execIntBindingT (IBT m) = execStateT m emptyIntBindingState

----------------------------------------------------------------

instance (Unifiable t, Applicative m, Monad m) =>
    BindingMonad IntVar t (IntBindingT t m)
    where
    
    lookupVar (IntVar v) = IBT $ gets (IM.lookup v . varBindings)
    
    freeVar = IBT $ do
        ibs <- get
        let v = nextFreeVar ibs
        if  v == maxBound
            then error "freeVar: no more variables!"
            else do
                put $ ibs { nextFreeVar = v+1 }
                return $ IntVar v
    
    newVar t = IBT $ do
        ibs <- get
        let v = nextFreeVar ibs
        if  v == maxBound
            then error "newVar: no more variables!"
            else do
                let bs' = IM.insert v t (varBindings ibs)
                put $ ibs { nextFreeVar = v+1, varBindings = bs' }
                return $ IntVar v
    
    bindVar (IntVar v) t = IBT $ do
        ibs <- get
        let bs' = IM.insert v t (varBindings ibs)
        put $ ibs { varBindings = bs' }

----------------------------------------------------------------
----------------------------------------------------------- fin.
