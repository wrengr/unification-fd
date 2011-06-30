{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2011.06.30
-- |
-- Module      :  Test1
-- Copyright   :  Copyright (c) 2009--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  test
-- Portability :  non-portable
--
-- Some basic tests to demonstrate correctness of the unification variants.
----------------------------------------------------------------
module Test1 where
import Data.Foldable
import Data.Traversable
import Data.List.Extras.Pair
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Error
import Control.Unification
import Control.Unification.Classes
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

data S a = S String [a]
    deriving (Read, Show, Eq, Ord, Functor, Foldable, Traversable)

instance Unifiable S where
    match (S a xs) (S b ys)
        | a == b    =
            case pair xs ys of
            Nothing    -> failure
            Just pairs -> more pairs
        | otherwise = failure
        
    zipMatch (S a xs) (S b ys)
        | a == b    = fmap (S a) (pair xs ys)
        | otherwise = Nothing

type STerm = MutTerm IntVar S 

test1 = print . runIdentity . evalIntBindingT $ eg1
    where
    eg1 = do
        -- Fundeps needed to avoid signatures for all calls to freeVar
        x <- freeVar
        y <- freeVar
        z <- freeVar
        let t1t0 = MutTerm$S "1" [MutTerm$S "0" []]
        let t1x  = MutTerm$S "1" [MutVar x]
        let t2xy = MutTerm$S "2" [MutVar x, MutVar y]
        let t2zz = MutTerm$S "2" [MutVar z, MutVar z]
        runErrorT $ do
            unify1 t1t0 t1x
            applyBindings t2xy

----------------------------------------------------------------
----------------------------------------------------------- fin.
