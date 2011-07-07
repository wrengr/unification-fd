
{-# LANGUAGE Rank2Types
           , MultiParamTypeClasses
           , UndecidableInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.07.06
-- |
-- Module      :  Control.Unification.Ranked.STVar
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  highly experimental
-- Portability :  semi-portable (Rank2Types, MPTCs,...)
--
-- A ranked variant of "Control.Unification.STVar".
----------------------------------------------------------------
module Control.Unification.Ranked.STVar
    ( STRVar()
    , STRBinding()
    , runSTRBinding
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)

import Data.STRef
import Data.Word            (Word8)
import Control.Applicative  (Applicative(..))
import Control.Monad        (ap)
import Control.Monad.Trans  (lift)
import Control.Monad.ST
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Unification.Types
----------------------------------------------------------------
----------------------------------------------------------------

-- | A ranked unification variable implemented by 'STRef's. In
-- addition to the @STRef@ for the term itself, we also track the
-- variable's ID (to support visited-sets) and rank (to support
-- weighted path compression).
data STRVar s t a =
    STRVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s Word8)
        {-# UNPACK #-} !(STRef s (Maybe (MutTerm (STRVar s t) t)))
-- BUG: can we actually unpack STRef?
-- BUG: we need a phantom @a@ to get the kinds to work out now...

instance Show (STRVar s t a) where
    show (STRVar i _ _) = "STRVar " ++ show i

instance Variable (STRVar s t) where
    eqVar (STRVar i _ _) (STRVar j _ _) = i == j
    
    getVarID  (STRVar i _ _) = i


----------------------------------------------------------------
-- TODO: parameterize this so we can use BacktrackST too. Or course,
-- that means defining another class for STRef-like variables
--
-- TODO: parameterize this so we can share the implementation for STVar and STRVar
--
-- TODO: does MTL still have the overhead that'd make it worthwhile
-- to do this manually instead of using ReaderT?
--
-- | A monad for handling 'STRVar' bindings.
newtype STRBinding s a = STRB { unSTRB :: ReaderT (STRef s Int) (ST s) a }


-- | Run the 'ST' ranked binding monad. N.B., because 'STRVar' are
-- rank-2 quantified, this guarantees that the return value has no
-- such references. However, in order to remove the references from
-- terms, you'll need to explicitly apply the bindings.
runSTRBinding :: (forall s. STRBinding s a) -> a
runSTRBinding stb =
    runST (newSTRef minBound >>= runReaderT (unSTRB stb))


-- For portability reasons, we're intentionally avoiding
-- -XDeriveFunctor, -XGeneralizedNewtypeDeriving, and the like.

instance Functor (STRBinding s) where
    fmap f = STRB . fmap f . unSTRB

instance Applicative (STRBinding s) where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad (STRBinding s) where
    return    = STRB . return
    stb >>= f = STRB (unSTRB stb >>= unSTRB . f)


----------------------------------------------------------------

_newSTRVar
    :: String
    -> Maybe (MutTerm (STRVar s t) t)
    -> STRBinding s (STRVar s t (MutTerm (STRVar s t) t))
_newSTRVar fun mb = STRB $ do
    nr <- ask
    lift $ do
        n <- readSTRef nr
        if n == maxBound
            then error $ fun ++ ": no more variables!"
            else do
                writeSTRef nr $! n+1
                -- BUG: no applicative ST
                rk  <- newSTRef 0
                ptr <- newSTRef mb
                return (STRVar n rk ptr)


instance (Unifiable t) => BindingMonad (STRVar s t) t (STRBinding s) where
    lookupVar (STRVar _ _ p) = STRB . lift $ readSTRef p
    
    freeVar  = _newSTRVar "freeVar" Nothing
    
    newVar t = _newSTRVar "newVar" (Just t)
    
    bindVar (STRVar _ _ p) t = STRB . lift $ writeSTRef p (Just t)


instance (Unifiable t) =>
    RankedBindingMonad (STRVar s t) t (STRBinding s)
    where
    
    lookupRankVar (STRVar _ r p) = STRB . lift $ do
        n  <- readSTRef r
        mb <- readSTRef p
        return (Rank n mb)
    
    incrementRank (STRVar _ r _) = STRB . lift $ do
        n <- readSTRef r
        writeSTRef r $! n+1
    
    -- incrementBindVar = default

----------------------------------------------------------------
----------------------------------------------------------- fin.
