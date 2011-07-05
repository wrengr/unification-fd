
{-# LANGUAGE Rank2Types
           , MultiParamTypeClasses
           , UndecidableInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.05
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
import Control.Applicative  (Applicative(..), (<$>))
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
data STVar s a = STVar {-# UNPACK #-} !Int {-# UNPACK #-} !(STRef s (Maybe a))
-- BUG: can we actually unpack STRef?


instance Show (STVar s a) where
    show (STVar i _) = "STVar " ++ show i


instance Variable (STVar s) where
    eqVar (STVar i _) (STVar j _) = i == j
    
    getVarID  (STVar i _) = i


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

instance BindingReader (STVar s) t (STBinding s) where
    lookupVar (STVar _ r) = STB . lift $ readSTRef r


_newSTVar :: String -> Maybe a -> STBinding s (STVar s a)
_newSTVar fun mb = STB $ do
    nr <- ask
    n  <- lift $ readSTRef nr
    if n == maxBound
        then fail $ fun ++ ": no more variables!"
        else lift $ do
            writeSTRef nr $! n+1
            STVar n <$> newSTRef mb


instance BindingGenerator (STVar s) t (STBinding s) where
    freeVar  = _newSTVar "freeVar" Nothing
    newVar t = _newSTVar "newVar" (Just t)


_writeSTVar :: STVar s a -> Maybe a -> STBinding s ()
_writeSTVar (STVar _ r) = STB . lift . writeSTRef r


instance BindingWriter (STVar s) t (STBinding s) where
    bindVar    v t = lookupVar v <* bindVar_   v t
    unbindVar  v   = lookupVar v <* unbindVar_ v
    
    bindVar_   v t = _writeSTVar v (Just t)
    unbindVar_ v   = _writeSTVar v Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
