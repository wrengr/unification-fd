
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.06
-- |
-- Module      :  Control.Unification.Ranked.IntVar
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  highly experimental
-- Portability :  semi-portable (MPTCs,...)
--
-- A ranked variant of "Control.Unification.IntVar".
----------------------------------------------------------------
module Control.Unification.Ranked.IntVar
    ( IntVar(..)
    , IntRBindingState()
    , IntRBindingT()
    , runIntRBindingT
    , evalIntRBindingT
    , execIntRBindingT
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)

import qualified Data.IntMap as IM
import Control.Applicative
import Control.Monad         (MonadPlus(..), liftM)
import Control.Monad.Trans   (MonadTrans(..))
import Control.Monad.State   (MonadState(..), StateT, runStateT, evalStateT, execStateT, gets)
import Control.Monad.Logic   (MonadLogic(..))
import Control.Unification.Types
import Control.Unification.IntVar (IntVar(..))
----------------------------------------------------------------
----------------------------------------------------------------

-- | Ranked binding state for 'IntVar'.
data IntRBindingState t = IntRBindingState
    { nextFreeVar :: {-# UNPACK #-} !Int
    , varBindings :: IM.IntMap (Rank IntVar t)
    }

-- Can't derive this because it's an UndecidableInstance
instance (Show (t (MutTerm IntVar t))) =>
    Show (IntRBindingState t)
    where
    show (IntRBindingState nr bs) =
        "IntRBindingState { nextFreeVar = "++show nr++
        ", varBindings = "++show bs++"}"

-- | The initial @IntRBindingState@.
emptyIntRBindingState :: IntRBindingState t
emptyIntRBindingState = IntRBindingState minBound IM.empty


----------------------------------------------------------------
-- | A monad for storing 'IntVar' bindings, implemented as a 'StateT'.
-- For a plain state monad, set @m = Identity@; for a backtracking
-- state monad, set @m = Logic@.
newtype IntRBindingT t m a = IRBT { unIRBT :: StateT (IntRBindingState t) m a }

-- For portability reasons, we're intentionally avoiding
-- -XDeriveFunctor, -XGeneralizedNewtypeDeriving, and the like.

instance (Functor m) => Functor (IntRBindingT t m) where
    fmap f = IRBT . fmap f . unIRBT

-- BUG: can't reduce dependency to Applicative because of StateT's instance.
instance (Functor m, Monad m) => Applicative (IntRBindingT t m) where
    pure    = IRBT . pure
    x <*> y = IRBT (unIRBT x <*> unIRBT y)
    x  *> y = IRBT (unIRBT x  *> unIRBT y)
    x <*  y = IRBT (unIRBT x <*  unIRBT y)

instance (Monad m) => Monad (IntRBindingT t m) where
    return  = IRBT . return
    m >>= f = IRBT (unIRBT m >>= unIRBT . f)

instance MonadTrans (IntRBindingT t) where
    lift = IRBT . lift

-- BUG: can't reduce dependency to Alternative because of StateT's instance.
instance (Functor m, MonadPlus m) => Alternative (IntRBindingT t m) where
    empty   = IRBT empty
    x <|> y = IRBT (unIRBT x <|> unIRBT y)

instance (MonadPlus m) => MonadPlus (IntRBindingT t m) where
    mzero       = IRBT mzero
    mplus ml mr = IRBT (mplus (unIRBT ml) (unIRBT mr))

instance (Monad m) => MonadState (IntRBindingState t) (IntRBindingT t m) where
    get = IRBT get
    put = IRBT . put

-- N.B., we already have (MonadLogic m) => MonadLogic (StateT s m),
-- provided that logict is compiled against the same mtl/monads-fd
-- we're getting StateT from. Otherwise we'll get a bunch of warnings
-- here.
instance (MonadLogic m) => MonadLogic (IntRBindingT t m) where
    msplit (IRBT m) = IRBT (coerce `liftM` msplit m)
        where
        coerce Nothing        = Nothing
        coerce (Just (a, m')) = Just (a, IRBT m')
    
    interleave (IRBT l) (IRBT r) = IRBT (interleave l r)
    
    IRBT m >>- f = IRBT (m >>- (unIRBT . f))
    
    ifte (IRBT b) t (IRBT f) = IRBT (ifte b (unIRBT . t) f)
    
    once (IRBT m) = IRBT (once m)

----------------------------------------------------------------

runIntRBindingT :: IntRBindingT t m a -> m (a, IntRBindingState t)
runIntRBindingT (IRBT m) = runStateT m emptyIntRBindingState


-- | N.B., you should explicitly apply bindings before calling this
-- function, or else the bindings will be lost
evalIntRBindingT :: (Monad m) => IntRBindingT t m a -> m a
evalIntRBindingT (IRBT m) = evalStateT m emptyIntRBindingState


execIntRBindingT :: (Monad m) => IntRBindingT t m a -> m (IntRBindingState t)
execIntRBindingT (IRBT m) = execStateT m emptyIntRBindingState

----------------------------------------------------------------

instance (Unifiable t, Applicative m, Monad m) =>
    BindingMonad IntVar t (IntRBindingT t m)
    where
    
    lookupVar (IntVar v) = IRBT $ do
        mb <- gets (IM.lookup v . varBindings)
        case mb of
            Nothing           -> return Nothing
            Just (Rank _ mb') -> return mb'
    
    freeVar = IRBT $ do
        ibs <- get
        let v = nextFreeVar ibs
        if  v == maxBound
            then error "freeVar: no more variables!"
            else do
                put $ ibs { nextFreeVar = v+1 }
                return $ IntVar v
    
    newVar t = IRBT $ do
        ibs <- get
        let v = nextFreeVar ibs
        if  v == maxBound
            then error "newVar: no more variables!"
            else do
                let bs' = IM.insert v (Rank 0 (Just t)) (varBindings ibs)
                put $ ibs { nextFreeVar = v+1, varBindings = bs' }
                return $ IntVar v
    
    bindVar (IntVar v) t = IRBT $ do
        ibs <- get
        let bs' = IM.insertWith f v (Rank 0 (Just t)) (varBindings ibs)
            f (Rank _0 jt) (Rank r _) = Rank r jt
        put $ ibs { varBindings = bs' }
    
    
instance (Unifiable t, Applicative m, Monad m) =>
    RankedBindingMonad IntVar t (IntRBindingT t m)
    where
    lookupRankVar (IntVar v) = IRBT $ do
        mb <- gets (IM.lookup v . varBindings)
        case mb of
            Nothing -> return (Rank 0 Nothing)
            Just rk -> return rk
    
    incrementRank (IntVar v) = IRBT $ do
        ibs <- get
        let bs' = IM.insertWith f v (Rank 1 Nothing) (varBindings ibs)
            f (Rank _1 _n) (Rank r mb) = Rank (r+1) mb
        put $ ibs { varBindings = bs' }
    
    incrementBindVar (IntVar v) t = IRBT $ do
        ibs <- get
        let bs' = IM.insertWith f v (Rank 1 (Just t)) (varBindings ibs)
            f (Rank _1 jt) (Rank r _) = Rank (r+1) jt
        put $ ibs { varBindings = bs' }

----------------------------------------------------------------
----------------------------------------------------------- fin.
