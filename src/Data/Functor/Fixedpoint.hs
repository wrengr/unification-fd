-- For the Show (Fix f) instance
{-# LANGUAGE UndecidableInstances #-}
-- For 'build' and 'hmap'
{-# LANGUAGE Rank2Types #-}

-- Unfortunately GHC < 6.10 needs -fglasgow-exts in order to actually
-- parse RULES (see -ddump-rules); the -frewrite-rules flag only
-- enables the application of rules, instead of doing what we want.
-- Apparently this is fixed in 6.10. In newer GHC (e.g., 7.6.1) the
-- -frewrite-rules flag is deprecated in favor of -fenable-rewrite-rules.
-- It's unclear whether we can use CPP to switch between -fglasgow-exts
-- -frewrite-rules and -fenable-rewrite-rules based on the GHC
-- version...
--
-- http://hackage.haskell.org/trac/ghc/ticket/2213
-- http://www.mail-archive.com/glasgow-haskell-users@haskell.org/msg14313.html
{-# OPTIONS_GHC -O2 -fenable-rewrite-rules #-}

-- NOTE #1: on GHC >= 7.8 we need to eta expand rules to avoid a
-- warning about the fact that the rule may never fire because (.)
-- might inline first...

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2014.05.28
-- |
-- Module      :  Data.Functor.Fixedpoint
-- Copyright   :  Copyright (c) 2007--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  semi-portable (Rank2Types)
--
-- This module provides a fixed point operator on functor types.
-- For Haskell the least and greatest fixed points coincide, so we
-- needn't distinguish them. This abstract nonsense is helpful in
-- conjunction with other category theoretic tricks like Swierstra's
-- functor coproducts (not provided by this package). For more on
-- the utility of two-level recursive types, see:
--
--     * Tim Sheard (2001) /Generic Unification via Two-Level Types/
--         /and Paramterized Modules/, Functional Pearl, ICFP.
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
      Fix(..)
    -- * Maps
    , hmap,  hmapM
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

----------------------------------------------------------------
----------------------------------------------------------------

-- | @Fix f@ is a fix point of the 'Functor' @f@. Note that in
-- Haskell the least and greatest fixed points coincide, so we don't
-- need to distinguish between @Mu f@ and @Nu f@. This type used
-- to be called @Y@, hence the naming convention for all the @yfoo@
-- functions.
--
-- This type lets us invoke category theory to get recursive types
-- and operations over them without the type checker complaining
-- about infinite types. The 'Show' instance doesn't print the
-- constructors, for legibility.
newtype Fix f = Fix { unFix :: f (Fix f) }

-- This requires UndecidableInstances because the context is larger
-- than the head and so GHC can't guarantee that the instance safely
-- terminates. It is in fact safe, however.
instance (Show (f (Fix f))) => Show (Fix f) where
    showsPrec p (Fix f) = showsPrec p f

instance (Eq (f (Fix f))) => Eq (Fix f) where
    Fix x == Fix y  =  x == y
    Fix x /= Fix y  =  x /= y

instance (Ord (f (Fix f))) => Ord (Fix f) where
    Fix x `compare` Fix y  =  x `compare` y
    Fix x >  Fix y         =  x >  y
    Fix x >= Fix y         =  x >= y
    Fix x <= Fix y         =  x <= y
    Fix x <  Fix y         =  x <  y
    Fix x `max` Fix y      =  Fix (max x y)
    Fix x `min` Fix y      =  Fix (min x y)

----------------------------------------------------------------

-- | A higher-order map taking a natural transformation @(f -> g)@
-- and lifting it to operate on @Fix@.
hmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> Fix f -> Fix g
{-# INLINE [0] hmap #-}
hmap eps = ana (eps . unFix)
    -- == cata (Fix . eps) -- But the anamorphism is a better producer.

{-# RULES
"hmap id"
        hmap id = id

-- cf., NOTE #1
"hmap-compose"
    forall (eps :: forall a. g a -> h a) (eta :: forall a. f a -> g a) x.
        hmap eps (hmap eta x) = hmap (eps . eta) x
    #-}


-- | A monadic variant of 'hmap'.
hmapM
    :: (Functor f, Traversable g, Monad m)
    => (forall a. f a -> m (g a)) -> Fix f -> m (Fix g)
{-# INLINE [0] hmapM #-}
hmapM eps = anaM (eps . unFix)

{-# RULES
"hmapM return"
    hmapM return = return

-- "hmapM-compose"
--     forall eps eta.
--         hmap eps <=< hmap eta = hmapM (eps <=< eta)
    #-}


-- | A version of 'fmap' for endomorphisms on the fixed point. That
-- is, this maps the function over the first layer of recursive
-- structure.
ymap :: (Functor f) => (Fix f -> Fix f) -> Fix f -> Fix f
{-# INLINE [0] ymap #-}
ymap f = Fix . fmap f . unFix

{-# RULES
"ymap id"
        ymap id = id

-- cf., NOTE #1
"ymap-compose"
    forall f g x.
        ymap f (ymap g x) = ymap (f . g) x
    #-}


-- | A monadic variant of 'ymap'.
ymapM :: (Traversable f, Monad m)
      => (Fix f -> m (Fix f)) -> Fix f -> m (Fix f)
{-# INLINE [0] ymapM #-}
ymapM f = liftM Fix . mapM f . unFix

{-# RULES
"ymapM id"
        ymapM return = return

-- "ymapM-compose"
--     forall f g.
--         ymapM f <=< ymapM g = ymapM (f <=< g)
    #-}


----------------------------------------------------------------
-- BUG: this isn't as helful as normal build\/fold fusion as in Data.Functor.Fusable
--
-- | Take a Church encoding of a fixed point into the data
-- representation of the fixed point.
build :: (Functor f) => (forall r. (f r -> r) -> r) -> Fix f
{-# INLINE [0] build #-}
build g = g Fix

-- N.B., the signature is required on @g@ in order to be Rank-2.
-- The signature is required on @phi@ in order to bring @f@ into
-- scope. Otherwise we'd need -XScopedTypeVariables.
{-# RULES
"build/cata" [1]
    forall (phi :: f a -> a) (g :: forall r. (f r -> r) -> r).
        cata phi (build g) = g phi
    #-}

----------------------------------------------------------------
-- | A pure catamorphism over the least fixed point of a functor.
-- This function applies the @f@-algebra from the bottom up over
-- @Fix f@ to create some residual value.
cata :: (Functor f) => (f a -> a) -> (Fix f -> a)
{-# INLINE [0] cata #-}
cata phi = self
    where
    self = phi . fmap self . unFix

{-# RULES
"cata-refl"
        cata Fix = id

-- cf., NOTE #1
"cata-compose"
    forall (eps :: forall a. f a -> g a) phi x.
        cata phi (cata (Fix . eps) x) = cata (phi . eps) x
    #-}

-- We can't really use this one because of the implication constraint
{- RULES
"cata-fusion"
    forall f phi. (f . phi) == (phi . fmap f) ==>
        f . cata phi = cata phi
-}


-- | A catamorphism for monadic @f@-algebras. Alas, this isn't wholly
-- generic to @Functor@ since it requires distribution of @f@ over
-- @m@ (provided by 'sequence' or 'mapM' in 'Traversable').
--
-- N.B., this orders the side effects from the bottom up.
cataM :: (Traversable f, Monad m) => (f a -> m a) -> (Fix f -> m a)
{-# INLINE [0] cataM #-}
cataM phiM = self
    where
    self = phiM <=< (mapM self . unFix)

-- TODO: other rules for cataM
{-# RULES
"cataM-refl"
        cataM (return . Fix) = return
    #-}


-- TODO: remove this, or add similar versions for ana* and hylo*?
-- | A variant of 'cata' which restricts the return type to being
-- a new fixpoint. Though more restrictive, it can be helpful when
-- you already have an algebra which expects the outermost @Fix@.
--
-- If you don't like either @fmap@ or @cata@, then maybe this is
-- what you were thinking?
ycata :: (Functor f) => (Fix f -> Fix f) -> Fix f -> Fix f
{-# INLINE ycata #-}
ycata f = cata (f . Fix)


-- TODO: remove this, or add similar versions for ana* and hylo*?
-- | Monadic variant of 'ycata'.
ycataM :: (Traversable f, Monad m)
       => (Fix f -> m (Fix f)) -> Fix f -> m (Fix f)
{-# INLINE ycataM #-}
ycataM f = cataM (f . Fix)


----------------------------------------------------------------
-- | A pure anamorphism generating the greatest fixed point of a
-- functor. This function applies an @f@-coalgebra from the top
-- down to expand a seed into a @Fix f@.
ana :: (Functor f) => (a -> f a) -> (a -> Fix f)
{-# INLINE [0] ana #-}
ana psi = self
    where
    self = Fix . fmap self . psi


{-# RULES
"ana-refl"
        ana unFix = id

-- BUG: I think I dualized this right...
-- cf., NOTE #1
"ana-compose"
    forall (eps :: forall a. f a -> g a) psi x.
        ana (eps . unFix) (ana psi x) = ana (eps . psi) x
    #-}

-- We can't really use this because of the implication constraint
{- RULES
-- BUG: I think I dualized this right...
"ana-fusion"
    forall f psi. (psi . f) == (fmap f . psi) ==>
        ana psi . f = ana psi
-}


-- | An anamorphism for monadic @f@-coalgebras. Alas, this isn't
-- wholly generic to @Functor@ since it requires distribution of
-- @f@ over @m@ (provided by 'sequence' or 'mapM' in 'Traversable').
--
-- N.B., this orders the side effects from the top down.
anaM :: (Traversable f, Monad m) => (a -> m (f a)) -> (a -> m (Fix f))
{-# INLINE anaM #-}
anaM psiM = self
    where
    self = (liftM Fix . mapM self) <=< psiM


----------------------------------------------------------------
-- Is this even worth mentioning? We can amortize the construction
-- of @Fix f@ (which we'd do anyways because of laziness), but we
-- can't fuse the @f@ away unless we inline all of @psi@, @fmap@,
-- and @phi@ at the use sites. Will inlining this definition be
-- sufficient to do that?

-- | @hylo phi psi == cata phi . ana psi@
hylo :: (Functor f) => (f b -> b) -> (a -> f a) -> (a -> b)
{-# INLINE hylo #-}
hylo phi psi = self
    where
    self = phi . fmap self . psi

-- TODO: rules for hylo?


-- | @hyloM phiM psiM == cataM phiM <=< anaM psiM@
hyloM :: (Traversable f, Monad m)
      => (f b -> m b) -> (a -> m (f a)) -> (a -> m b)
{-# INLINE hyloM #-}
hyloM phiM psiM = self
    where
    self = phiM <=< mapM self <=< psiM

-- TODO: rules for hyloM?

----------------------------------------------------------------
----------------------------------------------------------- fin.
