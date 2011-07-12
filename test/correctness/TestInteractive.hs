{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2011.07.11
-- |
-- Module      :  TestInteractive
-- Copyright   :  Copyright (c) 2009--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  test
-- Portability :  non-portable
--
-- An interactive testbed for playing around with things.
----------------------------------------------------------------
module TestInteractive where
import Data.Foldable
import Data.Traversable
import Data.List.Extras.Pair
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.MaybeK
import Control.Monad.EitherK
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

s :: String -> [STerm] -> STerm
s = (MutTerm .) . S

foo1 :: STerm -> STerm
foo1 x = s "foo" [x]

foo2 :: STerm -> STerm -> STerm
foo2 x y = s "foo" [x,y]

bar1 :: STerm -> STerm
bar1 x = s "bar" [x]

baz0 :: STerm
baz0 = s "baz" []

withNVars :: (Show a) => Int -> ([STerm] -> IntBindingT S Identity a) -> IO ()
withNVars = \n io -> print . runIdentity . runIntBindingT $ go [] n io
    where
    go xs 0 io = io (reverse xs)
    go xs n io = do x <- freeVar ; go (MutVar x : xs) (n-1) io

test1 = withNVars 2 $ \[x,y] -> runErrorT $ do
    let t10  = bar1 baz0
        t1x  = bar1 x
        t2xy = foo2 x y
        t200 = foo2 baz0 baz0
    --
    _ <- unify t10 t1x
    _ <- unify x y
    -- This should succeed, but will fail if the visited-set doesn't backtrack properly when coming up from recursion
    unify t200 t2xy

----------------------------------------------------------------
----------------------------------------------------------- fin.
