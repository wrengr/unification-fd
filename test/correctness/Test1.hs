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
import Control.Unification.Types
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

data S a = S String [a]
    deriving (Read, Show, Eq, Ord, Functor, Foldable, Traversable)

instance Unifiable S where
    zipMatch (S a xs) (S b ys)
        | a == b    = fmap (S a) (pair xs ys)
        | otherwise = Nothing

type STerm = MutTerm IntVar S 

test1 = print . runIdentity . runIntBindingT $ eg1
    where
    eg1 = do
        -- Fundeps needed to avoid signatures for all calls to freeVar
        x <- freeVar
        y <- freeVar
        let t0   = MutTerm$S "0" []
        let t10  = MutTerm$S "1" [MutTerm$S "0" []]
        let t1x  = MutTerm$S "1" [MutVar x]
        let t2xy = MutTerm$S "2" [MutVar x, MutVar y]
        let t200 = MutTerm$S "2" [t0,t0]
        runErrorT $ do
            _ <- unify t10 t1x
            _ <- unify (MutVar x) (MutVar y)
            -- This should succeed, but will fail if the visited-set doesn't backtrack properly when comming up from recursion
            unify t200 t2xy

----------------------------------------------------------------
----------------------------------------------------------- fin.
