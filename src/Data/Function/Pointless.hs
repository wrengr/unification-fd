{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2011.06.18
-- |
-- Module      :  Data.Function.Pointless
-- Copyright   :  Copyright (c) 2009--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- Pointless fun :)
----------------------------------------------------------------
module Data.Function.Pointless
    (
    -- * Multicomposition
    --
    -- Based on <http://matt.immute.net/content/pointless-fun>.
    -- These combinators allow you to easily modify the types of a
    -- many-argument function with syntax that looks like giving
    -- type signatures. For example,
    --
    -- > foo    :: A -> B -> C
    -- >
    -- > albert :: A -> X
    -- > beth   :: B -> Y
    -- > carol  :: C -> Z
    -- > 
    -- > bar :: X -> Y -> Z
    -- > bar = foo $:: albert ~> beth ~> carol
      ($::), (~>), (!~>)
    
    -- * Composition for arity 2
    , (...), (.^)
    
    -- * Strict composition
    , (.!)
    ) where
----------------------------------------------------------------
----------------------------------------------------------------

-- | Lift a function for multicomposition. This is like the @::@
-- of a type signature.

($::) :: (a -> b) -> ((a -> b) -> (c -> d)) -> (c -> d)
($::) = flip ($)
{-# INLINE ($::) #-}
infixl 1 $::


-- | Multicompose a function on the appropriate argument. This is
-- like the @->@ arrows in a type signature.

(~>)  :: (a -> b) -> (c -> d) -> ((b -> c) -> (a -> d))
f ~> g = (. f) . (g .)
{-# INLINE (~>) #-}
infixr 2 ~>


-- | Multicompose a function on the appropriate argument, calling
-- the left function eagerly. That is, the resulting function will
-- be strict in @a@ if the left argument is strict in @a@ (assuming
-- the final function of the multicomposition, the one applied to
-- the return value, is also strict).

(!~>)  :: (a -> b) -> (c -> d) -> ((b -> c) -> (a -> d))
f !~> g = (.! f) . (g .)
{-# INLINE (!~>) #-}
infixr 2 !~>


----------------------------------------------------------------
-- | Binary composition: pass two args to the right argument before
-- composing.
--
-- > (f ... g) x y = f (g x y)
--
-- This is the same as the common idiom @(f .) . g@ but more easily
-- extended to multiple uses, due to the fixity declaration.

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(...) = (.) . (.)
{-# INLINE (...) #-}
infixl 8 ...


-- | Secondary composition: compose the right argument on the second
-- arg of the left argument.
--
-- > (f .^ g) x y = f x (g y)

(.^) :: (a -> c -> d) -> (b -> c) -> (a -> b -> d)
(.^) = flip ... (.) . flip
{-# INLINE (.^) #-}
infix 9 .^


-- | Function composition which calls the right-hand function
-- eagerly; i.e., making the left-hand function strict in its first
-- argument.
--
-- > (f .! g) x = f $! g x
--
-- This defines the composition for the sub-category of strict
-- Haskell functions. If the 'Functor' class were parameterized by
-- the domain and codomain categories (e.g., a regular @Functor f@
-- would be @CFunctor (->) (->) f@ instead) then this would allow
-- us to define functors @CFunctor (->) (!->) f@ where
-- @fmap f . fmap g = fmap (f .! g)@.

(.!) :: (b -> c) -> (a -> b) -> a -> c
(.!) = (.) . ($!)
{-# INLINE (.!) #-}
infixr 9 .!
-- For some reason this definition is significantly faster than the
-- pointful version in the documentation. Even after INLINE. Who knew?
--
-- cf vs @($!) ... (.)@ == @\f g x -> f . g $! x@ which stictifies
-- the first argument of RH-function. However, this doesn't behave
-- the way you may think it should; i.e., it isn't compositional
-- in the way you think it should be.

----------------------------------------------------------------
----------------------------------------------------------- fin.
