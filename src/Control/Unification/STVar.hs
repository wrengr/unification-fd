
{-# LANGUAGE Rank2Types
           , MultiParamTypeClasses
           , UndecidableInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.06
-- |
-- Module      :  Control.Unification.STVar
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (Rank2Types, MPTCs, Undecidable-, FlexibleInstances)
--
-- This module defines an implementation of mutable unification
-- variables using the 'ST' monad.
----------------------------------------------------------------
module Control.Unification.STVar
    ( STVar()
    , STBinding()
    , runSTBinding
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)

import Data.STRef
import Data.Int             (Int8)
import Control.Applicative  (Applicative(..))
import Control.Monad        (ap)
import Control.Monad.Trans  (lift)
import Control.Monad.ST
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Unification.Classes
----------------------------------------------------------------
----------------------------------------------------------------

-- | A mutable unification variable implemented by an 'STRef'. In
-- addition to the @STRef@ itself, we also track an orderable ID
-- in order to use visited sets instead of occurance checks.
data STVar s t a =
    STVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s Int8)
        {-# UNPACK #-} !(STRef s (Maybe (MutTerm (STVar s t) t)))
-- BUG: can we actually unpack STRef?
-- BUG: we need a phantom @a@ to get the kinds to work out now...


instance Show (STVar s t a) where
    show (STVar i _ _) = "STVar " ++ show i


instance Variable (STVar s t) where
    eqVar (STVar i _ _) (STVar j _ _) = i == j
    
    getVarID  (STVar i _ _) = i


----------------------------------------------------------------
-- TODO: parameterize this so we can use BacktrackST too. Or course,
-- that means defining another class for STRef-like variables
--
-- TODO: does MTL still have the overhead that'd make it worthwhile
-- to do this manually instead of using ReaderT?
--
-- | A monad for handling 'STVar' bindings.
newtype STBinding s a = STB { unSTB :: ReaderT (STRef s Int) (ST s) a }


-- | Run the 'ST' binding monad. N.B., because 'STVar' are rank-2
-- quantified, this guarantees that the return value has no such
-- references. However, in order to remove the references from
-- terms, you'll need to explicitly apply the bindings.
runSTBinding :: (forall s. STBinding s a) -> a
runSTBinding stb =
    runST (newSTRef minBound >>= runReaderT (unSTB stb))


-- For portability reasons, we're intentionally avoiding
-- -XDeriveFunctor, -XGeneralizedNewtypeDeriving, and the like.

instance Functor (STBinding s) where
    fmap f = STB . fmap f . unSTB

instance Applicative (STBinding s) where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad (STBinding s) where
    return    = STB . return
    stb >>= f = STB (unSTB stb >>= unSTB . f)


----------------------------------------------------------------

_newSTVar
    :: String
    -> Maybe (MutTerm (STVar s t) t)
    -> STBinding s (STVar s t (MutTerm (STVar s t) t))
_newSTVar fun mb = STB $ do
    nr <- ask
    n  <- lift $ readSTRef nr
    if n == maxBound
        then fail $ fun ++ ": no more variables!"
        else lift $ do
            writeSTRef nr $! n+1
            rk  <- newSTRef 0
            ptr <- newSTRef mb
            return (STVar n rk ptr)


instance (Unifiable t) => BindingMonad (STVar s t) t (STBinding s) where
    lookupRankVar (STVar _ r p) = STB . lift $ do
        n  <- readSTRef r
        mb <- readSTRef p
        return (Rank n mb)
    
    lookupVar (STVar _ _ p) = STB . lift $ readSTRef p
    
    freeVar  = _newSTVar "freeVar" Nothing
    newVar t = _newSTVar "newVar" (Just t)
    
    bindVar (STVar _ _ p) t = STB . lift $ writeSTRef p (Just t)
    
    incrementRank (STVar _ r _) = STB . lift $ do
        n <- readSTRef r
        writeSTRef r $! n+1
    
    -- incrementBindVar = default

----------------------------------------------------------------
----------------------------------------------------------- fin.
