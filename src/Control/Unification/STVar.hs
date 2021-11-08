{-# LANGUAGE CPP
           , Rank2Types
           , MultiParamTypeClasses
           , UndecidableInstances
           , FlexibleInstances
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2021.11.07
-- |
-- Module      :  Control.Unification.STVar
-- Copyright   :  Copyright (c) 2007--2021 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@cpan.org
-- Stability   :  experimental
-- Portability :  semi-portable (Rank2Types, MPTCs,...)
--
-- This module defines an implementation of unification variables
-- using the 'ST' monad.
----------------------------------------------------------------
module Control.Unification.STVar
    ( STVar()
    , STBinding()
    , runSTBinding
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)

import Data.STRef
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative  (Applicative(..), (<$>))
#endif
import Control.Monad.Trans  (lift)
import Control.Monad.ST
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Unification.Types
----------------------------------------------------------------
----------------------------------------------------------------

-- | Unification variables implemented by 'STRef's. In addition to
-- the @STRef@ for the term itself, we also track the variable's
-- ID (to support visited-sets).
data STVar s t =
    STVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s (Maybe (UTerm t (STVar s t))))

instance Show (STVar s t) where
    show (STVar i _) = "STVar " ++ show i

instance Eq (STVar s t) where
    (STVar i _) == (STVar j _) = (i == j)

instance Variable (STVar s t) where
    getVarID (STVar i _) = i


----------------------------------------------------------------
-- TODO: parameterize this so we can use BacktrackST too. Or course,
-- that means defining another class for STRef-like variables
--
-- TODO: parameterize this so we can share the implementation for STVar and STRVar
--
-- TODO: does MTL still have the overhead that'd make it worthwhile
-- to do this manually instead of using ReaderT?
--
-- | A monad for handling 'STVar' bindings.
newtype STBinding s a = STB { unSTB :: ReaderT (STRef s Int) (ST s) a }


-- | Run the 'ST' ranked binding monad. N.B., because 'STVar' are
-- rank-2 quantified, this guarantees that the return value has no
-- such references. However, in order to remove the references from
-- terms, you'll need to explicitly apply the bindings and ground
-- the term.
runSTBinding :: (forall s. STBinding s a) -> a
runSTBinding stb =
    runST (newSTRef minBound >>= runReaderT (unSTB stb))
    -- N.B., because of the rank-2 quantification, cannot use the
    -- 'STB' pattern in lieu of 'unSTB' here.


-- For portability reasons, we're intentionally avoiding
-- -XDeriveFunctor, -XGeneralizedNewtypeDeriving, and the like.

instance Functor (STBinding s) where
    fmap f = STB . fmap f . unSTB

instance Applicative (STBinding s) where
    pure            = STB . pure
    STB m <*> STB n = STB (m <*> n)
    STB m  *> STB n = STB (m  *> n)
    STB m <*  STB n = STB (m <*  n)

-- Since base-4.8 (ghc-7.10.1) we have the default @return = pure@.
-- Since ghc-9.2.1 we get a warning about providing any other
-- definition, and should instead define both 'pure' and @(*>)@
-- directly, leaving 'return' and @(>>)@ as their defaults so they
-- can eventually be removed from the class.
-- <https://gitlab.haskell.org/ghc/ghc/-/wikis/proposal/monad-of-no-return>
instance Monad (STBinding s) where
#if (!(MIN_VERSION_base(4,8,0)))
    return    = pure
    (>>)      = (*>)
#endif
    STB m >>= f = STB (m >>= unSTB . f)


----------------------------------------------------------------

_newSTVar
    :: String
    -> Maybe (UTerm t (STVar s t))
    -> STBinding s (STVar s t)
_newSTVar fun mb = STB $ do
    nr <- ask
    lift $ do
        n <- readSTRef nr
        if n == maxBound
            then error $ fun ++ ": no more variables!"
            else do
                writeSTRef nr $! n+1
                STVar n <$> newSTRef mb

instance (Unifiable t) =>
    BindingMonad t (STVar s t) (STBinding s)
    where

    lookupVar (STVar _ p) = STB . lift $ readSTRef p

    freeVar  = _newSTVar "freeVar" Nothing

    newVar t = _newSTVar "newVar" (Just t)

    bindVar (STVar _ p) t = STB . lift $ writeSTRef p (Just t)

----------------------------------------------------------------
----------------------------------------------------------- fin.
