-- For 'build', 'hmap', and 'hmapM'
{-# LANGUAGE Rank2Types #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2024-11-20
-- |
-- Module      :  Data.Functor.Fixedpoint
-- Copyright   :  Copyright (c) 2007--2024 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@cpan.org
-- Stability   :  deprecated since unification-fd-0.12.0
-- Portability :  semi-portable (Rank2Types)
--
-- This module provides a backwards compatibility shim for users
-- of older versions of @unification-fd@, before we switched over
-- to using @data-fix@.  New users should prefer calling @data-fix@
-- functions directly, whenever possible.  If you use any of the
-- functions that aren't deprecated ('hoistFixM'', 'ymap', 'ymapM',
-- 'ycata', 'ycataM', 'build'), please let the maintainer know,
-- so she can focus on getting those incorporated into @data-fix@.
-- Returning users should beware that this module used to provide
-- rewrite rules for fusing redundant traversals of data structures
-- (which @data-fix@ does not).  If you notice version >=0.12.0
-- introducing any performance loss compared to earlier versions,
-- please let the maintainer know, so she can focus on getting those
-- incorporated into @data-fix@.
--
-- This abstract nonsense is helpful in conjunction with other
-- category theoretic tricks like Swierstra's functor coproducts
-- (not provided by this package). For more on the utility of
-- two-level recursive types, see:
--
--     * Tim Sheard (2001) /Generic Unification via Two-Level Types/
--         /and Parameterized Modules/, Functional Pearl, ICFP.
--
--     * Tim Sheard & Emir Pasalic (2004) /Two-Level Types and/
--         /Parameterized Modules/. JFP 14(5): 547--587. This is
--         an expanded version of Sheard (2001) with new examples.
--
--     * Wouter Swierstra (2008) /Data types a la carte/, Functional
--         Pearl. JFP 18: 423--436.
----------------------------------------------------------------

module Data.Functor.Fixedpoint
    (
    -- * Fixed point operator for functors
      Data.Fix.Fix(..)
    -- * Maps
    , hmap,  hmapM, hoistFixM'
    , ymap,  ymapM
    -- * Builders
    , build
    -- * Catamorphisms
    , cata,  cataM
    , ycata, ycataM
    -- * Anamorphisms
    , ana,   anaM
    -- * Hylomorphisms
    , hylo,  hyloM
    ) where

import Prelude          hiding (mapM, sequence)
import Control.Monad    hiding (mapM, sequence)
import Data.Traversable
import Data.Fix (Fix())
import qualified Data.Fix

----------------------------------------------------------------
----------------------------------------------------------------

-- | A higher-order map taking a natural transformation @(f -> g)@
-- and lifting it to operate on @Fix@.
--
-- NOTE: The implementation of @hmap@ prior to version 0.12 was
-- based on 'ana', and therefore most closely matches the behavior
-- of 'Data.Fix.hoistFix''.  However, this definition is extensionally
-- equivalent to an implementation using 'cata' (and therefore most
-- closely matches the behavior of 'Data.Fix.hoistFix') instead.
hmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> Fix f -> Fix g
hmap = Data.Fix.hoistFix'
{-# DEPRECATED hmap "Use Data.Fix.hoistFix'" #-}

-- | A monadic variant of 'hmap'.
hmapM
    :: (Functor f, Traversable g, Monad m)
    => (forall a. f a -> m (g a)) -> Fix f -> m (Fix g)
hmapM = hoistFixM'
{-# DEPRECATED hmapM "Use hoistFixM'" #-}

-- | A monadic variant of 'Data.Fix.hoistFix''.
--
-- NOTE: The implementation of @hmapM@ prior to version 0.12 was
-- based on 'anaM', and therefore most closely matches the behavior
-- of 'Data.Fix.unfoldFixM'. However, there is another function
-- of the same type which is instead implemented via 'cataM',
-- which has different semantics for many monads.
hoistFixM'
    :: (Functor f, Traversable g, Monad m)
    => (forall a. f a -> m (g a)) -> Fix f -> m (Fix g)
hoistFixM' eps = Data.Fix.unfoldFixM (eps . Data.Fix.unFix)

-- | A version of 'fmap' for endomorphisms on the fixed point. That
-- is, this maps the function over the first layer of recursive
-- structure.
ymap :: (Functor f) => (Fix f -> Fix f) -> Fix f -> Fix f
ymap f = Data.Fix.Fix . fmap f . Data.Fix.unFix

-- | A monadic variant of 'ymap'.
ymapM :: (Traversable f, Monad m)
      => (Fix f -> m (Fix f)) -> Fix f -> m (Fix f)
ymapM f = liftM Data.Fix.Fix . mapM f . Data.Fix.unFix


----------------------------------------------------------------
-- BUG: this isn't as helful as normal build\/fold fusion as in Data.Functor.Fusable
--
-- | Take a Church encoding of a fixed point into the data
-- representation of the fixed point.
build :: (Functor f) => (forall r. (f r -> r) -> r) -> Fix f
build g = g Data.Fix.Fix

----------------------------------------------------------------
-- | A pure catamorphism over the least fixed point of a functor.
-- This function applies the @f@-algebra from the bottom up over
-- @Fix f@ to create some residual value.
cata :: (Functor f) => (f a -> a) -> (Fix f -> a)
cata = Data.Fix.foldFix
{-# DEPRECATED cata "Use Data.Fix.foldFix" #-}


-- | A catamorphism for monadic @f@-algebras. Alas, this isn't wholly
-- generic to @Functor@ since it requires distribution of @f@ over
-- @m@ (provided by 'sequence' or 'mapM' in 'Traversable').
--
-- N.B., this orders the side effects from the bottom up.
cataM :: (Traversable f, Monad m) => (f a -> m a) -> (Fix f -> m a)
cataM = Data.Fix.foldFixM
{-# DEPRECATED cataM "Use Data.Fix.foldFixM" #-}

-- TODO: remove this, or add similar versions for ana* and hylo*?
-- | A variant of 'cata' which restricts the return type to being
-- a new fixpoint. Though more restrictive, it can be helpful when
-- you already have an algebra which expects the outermost @Fix@.
--
-- If you don't like either @fmap@ or @cata@, then maybe this is
-- what you were thinking?
ycata :: (Functor f) => (Fix f -> Fix f) -> Fix f -> Fix f
ycata f = Data.Fix.foldFix (f . Data.Fix.Fix)


-- TODO: remove this, or add similar versions for ana* and hylo*?
-- | Monadic variant of 'ycata'.
ycataM :: (Traversable f, Monad m)
       => (Fix f -> m (Fix f)) -> Fix f -> m (Fix f)
ycataM f = Data.Fix.foldFixM (f . Data.Fix.Fix)


----------------------------------------------------------------
-- | A pure anamorphism generating the greatest fixed point of a
-- functor. This function applies an @f@-coalgebra from the top
-- down to expand a seed into a @Fix f@.
ana :: (Functor f) => (a -> f a) -> (a -> Fix f)
ana = Data.Fix.unfoldFix
{-# DEPRECATED ana "Use Data.Fix.unfoldFix" #-}

-- | An anamorphism for monadic @f@-coalgebras. Alas, this isn't
-- wholly generic to @Functor@ since it requires distribution of
-- @f@ over @m@ (provided by 'sequence' or 'mapM' in 'Traversable').
--
-- N.B., this orders the side effects from the top down.
anaM :: (Traversable f, Monad m) => (a -> m (f a)) -> (a -> m (Fix f))
anaM = Data.Fix.unfoldFixM
{-# DEPRECATED anaM "Use Data.Fix.unfoldFixM" #-}


----------------------------------------------------------------
-- | @hylo phi psi == cata phi . ana psi@
hylo :: (Functor f) => (f b -> b) -> (a -> f a) -> (a -> b)
hylo = Data.Fix.refold
{-# DEPRECATED hylo "Use Data.Fix.refold" #-}

-- | @hyloM phiM psiM == cataM phiM <=< anaM psiM@
hyloM :: (Traversable f, Monad m)
      => (f b -> m b) -> (a -> m (f a)) -> (a -> m b)
hyloM = Data.Fix.refoldM
{-# DEPRECATED hyloM "Use Data.Fix.refoldM" #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
