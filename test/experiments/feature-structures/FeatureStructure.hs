{-# LANGUAGE DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2021.10.17
-- |
-- Module      :  FeatureStructure
-- Copyright   :  Copyright (c) 2012--2021 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@cpan.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An implementation of feature structures, to test for feasibility.
----------------------------------------------------------------
module FeatureStructure where

import Prelude hiding
    ( mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1
    , any, all, and, or, elem
    )
import qualified Data.Map as M
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Unification
import Control.Unification.IntVar
import Control.Monad.Error    (ErrorT(..))
import Control.Monad.Identity (Identity(..))
----------------------------------------------------------------
----------------------------------------------------------------

type FSTerm k = UTerm (FS k) IntVar

newtype FS k a = FS (M.Map k a)
    deriving (Show, Functor, Foldable, Traversable)

type FSError k = UnificationFailure (FS k) IntVar

evalFS
    :: ErrorT (FSError k) (IntBindingT (FS k) Identity) a
    -> Either (FSError k) a
evalFS
    = runIdentity
    . evalIntBindingT
    . runErrorT

emptyFS :: Ord k => FSTerm k
emptyFS = UTerm $ FS M.empty

conFS :: Ord k => k -> FSTerm k -> FSTerm k
conFS k = UTerm . FS . M.singleton k

consFS :: Ord k => [(k, FSTerm k)] -> FSTerm k
consFS = UTerm . FS . M.fromList

flatFS :: Ord k => [k] -> FSTerm k
flatFS = UTerm . FS . M.fromList . map (\k -> (k, emptyFS))


-- BUG: need the new containers library to actually merge efficiently
instance (Ord k) => Unifiable (FS k) where
    zipMatch (FS ls) (FS rs) =
        Just . FS $ M.unionWith (\(Left l) (Left r) -> Right (l,r))
            (fmap Left ls)
            (fmap Left rs)


----------------------------------------------------------------
----------------------------------------------------------- fin.
