
{-# LANGUAGE Rank2Types
           , MultiParamTypeClasses
           , FunctionalDependencies
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

----------------------------------------------------------------
--                                                  ~ 2011.07.05
-- |
-- Module      :  Control.Unification.Classes
-- Copyright   :  Copyright (c) 2007--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (Rank2Types, MPTCs, fundeps)
--
-- This module defines the classes used by unification and related
-- functions.
----------------------------------------------------------------
module Control.Unification.Classes
    (
    -- * Classes for unification variable bindings
      BindingReader(..)
    , BindingGenerator(..)
    , BindingWriter(..)
    -- * Classes for equality, subsumption, and unification
    , Unifiable(..)
    , Variable(..)
    -- ** Abstract type for continuations in equality, etc
    , More()
    , getMore
    , more
    , success
    , failure
    ) where

import Prelude hiding (mapM, sequence, foldr, foldr1, foldl, foldl1)
import qualified Prelude (foldr)

import Data.Traversable    (Traversable())
import Control.Applicative (Applicative())
import Control.Monad       (MonadPlus(..))
import Control.Monad.Logic (Logic(..), LogicT(..))
----------------------------------------------------------------
----------------------------------------------------------------

-- TODO: since nearly all the readers will (semi)prune paths, should this just be combined with the BindingWriter class? Or maybe we should move semipruning into here?
--
-- | A class for reading from bindings stored in a monad.
class (Variable v, Applicative m, Monad m) =>
    BindingReader v t m | m -> v t
    where
    -- | Given a variable pointing to @t@, return the @t@ it's bound
    -- to, or @Nothing@ if the variable is unbound.
    lookupVar :: v t -> m (Maybe t)
    
    -- TODO: for weighted path compression. Should probably be rolled into 'lookupVar' no doubt...
    -- lookupVarRank :: v t -> m Int

{-
class (Variable v, Functor m, Monad m) => BindingReifyer v t m where
    -- Return all the bindings as a mapping from variables to terms. But how? What type to use for (:->:) ? And this isn't even always possible (e.g., using STVars; we'd have to do extra work to keep track of the bindings).
    getBindings :: m (v t :->: t)
-}


-- | A class for non-destructive modification of the bindings stored
-- in a monad, namely allocating new free and bound unification
-- variables.
class (Variable v, Applicative m, Monad m) =>
    BindingGenerator v t m | m -> v t
    where
    -- | Generate a new free variable guaranteed to be fresh in
    -- @m@.
    freeVar :: m (v t)
    
    -- | Generate a new variable (fresh in @m@) bound to the given
    -- term.
    newVar :: t -> m (v t)


-- | A class for potentially destructive modification of the bindings
-- stored in a monad.
class (Variable v, Applicative m, Monad m) =>
    BindingWriter v t m | m -> v t
    where
    -- | Bind a variable to a term, returning the old binding if
    -- any.
    bindVar :: v t -> t -> m (Maybe t)
    
    -- | Bind a variable to a term.
    bindVar_ :: v t -> t -> m ()
    bindVar_ v t = bindVar v t >> return ()
    
    -- | Remove a variable binding, returning the old binding if
    -- any.
    unbindVar :: v t -> m (Maybe t)
    
    -- | Remove a variable binding.
    unbindVar_ :: v t -> m ()
    unbindVar_ v = unbindVar v >> return ()


----------------------------------------------------------------

-- TODO: use MaybeK
-- | An abstract type representing a list of pairs of terms to
-- continue unifying, testing for equality, etc.
newtype More a b = More (Maybe (Logic (a,b)))

-- | For internal use.
getMore :: More a b -> Maybe (Logic (a,b))
getMore (More mb) = mb

-- TODO: send a patch defining [a] -> Logic a to logict
more :: [(a,b)] -> More a b
more xs = More . Just . Logic . LogicT $ \ks kf -> Prelude.foldr ks kf xs

success :: More a b
success = More $ Just mzero

failure :: More a b
failure = More Nothing


-- | An implementation of unifiable structure.
class (Traversable t) => Unifiable t where
    -- | Perform one level of equality testing for terms. If the
    -- term constructors are unequal then return 'failure'; if they
    -- are equal, then return the subterms to be recursively checked
    -- (e.g., with 'more' to pair off the corresponding sub-terms,
    -- or 'success' if the constructors have no sub-terms).
    match :: t a -> t b -> More a b
    
    -- Perhaps this would be enough for the aggressive obs.sharing? (in conjunction with traverse/mapM)
    zipMatch :: t a -> t b -> Maybe (t (a,b))


-- | An implementation of unification variables.
class Variable v where
    -- | Determine whether two variables are equal /as variables/,
    -- without considering what they are bound to.
    eqVar :: v a -> v a -> Bool
    
    -- | Return a unique identifier for this variable, in order to
    -- support the use of visited-sets instead of occurs checks.
    getVarID :: v a -> Int

----------------------------------------------------------------
----------------------------------------------------------- fin.
