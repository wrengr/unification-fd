
{-# LANGUAGE MultiParamTypeClasses
           , TypeOperators
           , FlexibleInstances
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

----------------------------------------------------------------
--                                                    2011.06.27
-- |
-- Module      :  Data.Functor.Coproduct
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (MPTCs, TypeOperators)
--
-- This module provides an extensible union type for functors.
--
--     * Wouter Swierstra (2008) /Data types a la carte/, Functional
--         Pearl. JFP 18: 423--436.
----------------------------------------------------------------

module Data.Functor.Coproduct
    (
    -- * Functor coproducts
      (:+:)(..)
    -- * Functor subtyping
    , (:<:)(..)
    -- ** Coproduct smart constructors\/destructors
    , asInjectedInto
    , asProjectionOf
    -- ** Fixed-point smart constructors\/destructors
    , asFixOf
    , asUnfixOf
    ) where

import Prelude hiding (foldr, foldl, foldr1, foldl1, mapM, sequence)

import Data.Functor.Fixedpoint
import Data.Foldable
import Data.Traversable
import Control.Applicative ((<$>))
import Control.Monad       (liftM)

----------------------------------------------------------------
----------------------------------------------------------------
-- There's a bug in Haddock 2.0.0.0 where it will drop parentheses
-- around strict fields, functions as arguments, etc. This is
-- apparently fixed in version 2.2.0
--
-- <http://trac.haskell.org/haddock/ticket/44>


-- | The coproduct of two @Functor@s is a @Functor@. It is a
-- @Foldable@ or @Traversable@ functor if the base functors are.
-- The @Show@ instance does not print the constructors, for legibility.
data (f :+: g) a = Inl !(f a) | Inr !(g a)
infixr 5 :+:

instance (Show (f a), Show (g a)) => Show ((f :+: g) a) where
    showsPrec n (Inl x) = showsPrec n x
    showsPrec n (Inr x) = showsPrec n x
    show        (Inl x) = show x
    show        (Inr x) = show x

-- TODO: is this really an endofunctor with the strictness?
-- BUG: for some reason, client code is losing the Functor instances
-- for f and g. Why?
instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl x) = Inl (fmap f x)
    fmap f (Inr y) = Inr (fmap f y)

-- BUG: for some reason, client code is losing the Foldable instances
-- for f and g. Why?
instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    fold      (Inl m) = fold m
    fold      (Inr m) = fold m
    foldMap f (Inl x) = foldMap f x
    foldMap f (Inr x) = foldMap f x
    foldr k z (Inl x) = foldr k z x
    foldr k z (Inr x) = foldr k z x
    foldl k z (Inl x) = foldl k z x
    foldl k z (Inr x) = foldl k z x
    foldr1 f  (Inl x) = foldr1 f x
    foldr1 f  (Inr x) = foldr1 f x
    foldl1 f  (Inl x) = foldl1 f x
    foldl1 f  (Inr x) = foldl1 f x

-- BUG: for some reason, client code is losing the Traversable
-- instances for f and g. Why?
instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl t)  = Inl <$> traverse f t
    traverse f (Inr t)  = Inr <$> traverse f t
    sequenceA  (Inl t)  = Inl <$> sequenceA t
    sequenceA  (Inr t)  = Inr <$> sequenceA t
    mapM     f (Inl x)  = Inl `liftM` mapM f x
    mapM     f (Inr x)  = Inr `liftM` mapM f x
    sequence   (Inl mx) = Inl `liftM` sequence mx
    sequence   (Inr mx) = Inr `liftM` sequence mx


----------------------------------------------------------------
----------------------------------------------------------------

-- | This class captures the subtyping relationship between a simple
-- functor and a coproduct functor. It is used for coercing between
-- the subtype and the supertype, and for defining smart constructors
-- to handle transitivity of the subtyping relation.
class (Functor sub, Functor sup) => sub :<: sup where
    
    -- | Inject a subtype into the supertype.
    inj :: sub a -> sup a
    
    -- | Project a subtype from the supertype, if possible.
    prj :: sup a -> Maybe (sub a)


-- BUG: alas, we can't use the infix notation when defining
-- instances. At least, not on older GHCs
instance (Functor f) => (:<:) f f where
    inj = id
    prj = Just

instance (Functor f, Functor g) => (:<:) f (f :+: g) where
    inj         = Inl
    prj (Inl x) = Just x
    prj (Inr _) = Nothing

instance (Functor f, Functor g, Functor h, f :<: g) => (:<:) f (h :+: g) where
    inj         = Inr . inj
    prj (Inl _) = Nothing
    prj (Inr y) = prj y


-- | A type-passing variant of 'inj' which injects a simple functor
-- into a given coproduct. This is named for infix use, like
-- 'asTypeOf'.
asInjectedInto :: (f :<: g) => f a -> g b -> g a
asInjectedInto = const . inj


-- | A type-passing variant of 'prj' which strips off the coproduct
-- if the underlying functor matches a given functor. This is named
-- for infix use, like 'asTypeOf'.
asProjectionOf :: (f :<: g) => g a -> f b -> Maybe (f a)
asProjectionOf = const . prj

----------------------------------------------------------------

-- | Inject a semi-fixed term into the coproduct of another given
-- term. This is most helpful when you don't know the coproduct
-- that the initial term recurses as. This is named for infix use,
-- like 'asTypeOf'.
asFixOf :: (f :<: g) => f (Fix g) -> Fix g -> Fix g
asFixOf = const . Fix . inj


-- | Take a fixed term, unfix the outermost iteration of the fixed
-- point, and then project out the underlying functor if it matches
-- another given semi-fixed term. This is named for infix use, like
-- 'asTypeOf'.
asUnfixOf :: (f :<: g) => Fix g -> f (Fix g) -> Maybe (f (Fix g))
asUnfixOf = const . prj . unFix

----------------------------------------------------------------
----------------------------------------------------------- fin.
