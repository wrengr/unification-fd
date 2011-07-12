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

-- N.B., don't go deeper than about 15 if you're printing the term.
fooN :: Int -> STerm
fooN n
    | n <= 0    = baz0
    | otherwise = let t = fooN $! n-1 in foo2 t t

fooNxl n
    | n <= 0    = return baz0
    | otherwise = do
        x <- MutVar <$> freeVar
        t <- fooNxl $! n-1
        return (foo2 x t)

fooNxr n
    | n <= 0    = return baz0
    | otherwise = do
        x <- MutVar <$> freeVar
        t <- fooNxr $! n-1
        return (foo2 t x)

withNVars :: (Show a) => Int -> ([STerm] -> IntBindingT S Identity a) -> IO ()
withNVars = \n io -> print . runIdentity . runIntBindingT $ go [] n io
    where
    go xs 0 io = io (reverse xs)
    go xs n io = do x <- freeVar ; go (MutVar x : xs) (n-1) io

test1 = withNVars 2 $ \[x,y] -> runEitherKT $ do
    let t10  = bar1 baz0
        t1x  = bar1 x
        t2xy = foo2 x y
        t200 = foo2 baz0 baz0
    --
    _ <- unify t10 t1x
    _ <- unify x y
    -- This should succeed, but will fail if the visited-set doesn't backtrack properly when coming up from recursion
    unify t200 t2xy

unifies []     = return ()
unifies [_]    = return ()
unifies (x:xs) = go xs x
    where
    go []     _ = return ()
    go (x:xs) y = unify x y >>= go xs


unifiesOccurs []     = return ()
unifiesOccurs [_]    = return ()
unifiesOccurs (x:xs) = go xs x
    where
    go []     _ = return ()
    go (x:xs) y = unifyOccurs x y >>= go xs

{-
A stupid benchmark demonstrating the occurs-check removal. We use @t@ to ensure the whole tree gets filled in since @tl@ and @tr@ are linear terms and we can unify them with each other by doing one bindVar

    print
    . runIdentity
    . runIntBindingT
    $ do
        tl <- fooNxl 15
        tr <- fooNxr 15
        let t = fooN 15
        runEitherKT (unifies [tl,t,tr])
            -- unifiesOccurs [tl,t,tr]
            -- unifies/Occurs [tl,tr,t]
            -- unifies/Occurs [tl,t,tr,t]
        return ()
-}
----------------------------------------------------------------
----------------------------------------------------------- fin.
