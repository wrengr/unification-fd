{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2012.03.16
-- |
-- Module      :  Codensity
-- Copyright   :  Copyright (c) 2007--2012 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Test the efficiency of 'MaybeK' vs 'Maybe'
----------------------------------------------------------------
module Codensity (main) where

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, and, or)

import Criterion.Main

import qualified Data.IntMap as IM
import Data.Foldable
import Data.Traversable
import Data.List.Extras.Pair
import Control.Applicative
import Control.Monad             (MonadPlus(..))
import Control.Monad.Trans       (MonadTrans(..))
import Control.Monad.Identity    (Identity(..))
import Control.Monad.State       (MonadState(..), execStateT)
import Control.Monad.MaybeK      (MaybeKT, runMaybeKT)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Unification
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

equalsK, equalsMb
    :: (BindingMonad t v m)
    => MutTerm t v  -- ^
    -> MutTerm t v  -- ^
    -> m Bool       -- ^

equalsK tl tr = do
    mb <- runMaybeKT (equals_loop tl tr)
    case mb of
        Nothing -> return False
        Just () -> return True

equalsMb tl tr = do
    mb <- runMaybeT (equals_loop tl tr)
    case mb of
        Nothing -> return False
        Just () -> return True

equals_loop
    :: (MonadTrans n, MonadPlus (n m), BindingMonad t v m)
    => MutTerm t v  -- ^
    -> MutTerm t v  -- ^
    -> n m ()       -- ^
{-# INLINE equals_loop #-}
equals_loop tl0 tr0 = do
        tl <- lift $ semiprune tl0
        tr <- lift $ semiprune tr0
        case (tl, tr) of
            (MutVar vl', MutVar vr')
                | vl' `eqVar` vr' -> return () -- success
                | otherwise       -> do
                    mtl <- lift $ lookupVar vl'
                    mtr <- lift $ lookupVar vr'
                    case (mtl, mtr) of
                        (Nothing,  Nothing ) -> mzero
                        (Nothing,  Just _  ) -> mzero
                        (Just _,   Nothing ) -> mzero
                        (Just tl', Just tr') -> equals_loop tl' tr' -- TODO: should just jump to match
            (MutVar  _,   MutTerm _  ) -> mzero
            (MutTerm _,   MutVar  _  ) -> mzero
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> mzero
                Just tlr -> mapM_ (uncurry equals_loop) tlr


----------------------------------------------------------------
equivK, equivMb
    :: (BindingMonad t v m)
    => MutTerm t v               -- ^
    -> MutTerm t v               -- ^
    -> m (Maybe (IM.IntMap Int)) -- ^
    
equivK  tl tr = runMaybeKT (execStateT (equiv_loop tl tr) IM.empty)
equivMb tl tr = runMaybeT  (execStateT (equiv_loop tl tr) IM.empty)

equiv_loop
    ::  ( MonadTrans n, MonadPlus (n m)
        , MonadTrans s, MonadState (IM.IntMap Int) (s (n m))
        , BindingMonad t v m
        )
    => MutTerm t v -- ^
    -> MutTerm t v -- ^
    -> s (n m) ()  -- ^
{-# INLINE equiv_loop #-}
equiv_loop tl0 tr0 = do
        tl <- lift . lift $ fullprune tl0
        tr <- lift . lift $ fullprune tr0
        case (tl, tr) of
            (MutVar vl',  MutVar  vr') -> do
                let il = getVarID vl'
                let ir = getVarID vr'
                xs <- get
                case IM.lookup il xs of
                    Just x
                        | x == ir   -> return ()
                        | otherwise -> lift mzero
                    Nothing         -> put $! IM.insert il ir xs
            
            (MutVar _,    MutTerm _  ) -> lift mzero
            (MutTerm _,   MutVar  _  ) -> lift mzero
            (MutTerm tl', MutTerm tr') ->
                case zipMatch tl' tr' of
                Nothing  -> lift mzero
                Just tlr -> mapM_ (uncurry equiv_loop) tlr
----------------------------------------------------------------


data S a = S String [a]
    deriving (Read, Show, Eq, Ord, Functor, Foldable, Traversable)

instance Unifiable S where
    zipMatch (S a xs) (S b ys)
        | a == b    = fmap (S a) (pair xs ys)
        | otherwise = Nothing

type STerm = MutTerm S IntVar

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

fooNxl :: (BindingMonad t IntVar f) => Int -> f STerm
fooNxl n
    | n <= 0    = return baz0
    | otherwise = do
        x <- MutVar <$> freeVar
        t <- fooNxl $! n-1
        return (foo2 x t)

fooNxr :: (BindingMonad t IntVar f) => Int -> f STerm
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

runIntBinding  = runIdentity . runIntBindingT
evalIntBinding = runIdentity . evalIntBindingT

runCriterionTests :: STerm -> STerm -> IO ()
runCriterionTests tl tr =
    defaultMain
        [ bgroup "equals (False)"
            [ bench "equalsK"  $ nf (evalIntBinding . equalsK  tl) tr
            , bench "equalsMb" $ nf (evalIntBinding . equalsMb tl) tr
            ]
        , bgroup "equals (True)"
            [ bench "equalsK"  $ nf (evalIntBinding . equalsK  tl) tl
            , bench "equalsMb" $ nf (evalIntBinding . equalsMb tl) tl
            ]
        {-
        -- BUG: No instances for (Control.DeepSeq.NFData (IntBindingState S),
                      Control.DeepSeq.NFData (IM.IntMap Int))
        , bgroup "equiv"
            [ bench "equivK"  $ nf (evalIntBinding . equivK  tl) tr
            , bench "equivMb" $ nf (evalIntBinding . equivMb tl) tr
            ]
        -}
        ]

test0
    = print
    . runIntBinding
    $ do
        tl <- fooNxl 15
        tr <- fooNxr 15
        sequence
            [ equalsK  tl tr
            , equalsMb tl tr
            , equalsK  tl tl
            , equalsMb tl tl
            , equalsK  tr tr
            , equalsMb tr tr
            ]

t0 =
    (foo2
        (foo2
            (foo2 baz0 baz0)
            (foo2 baz0 baz0))
        (foo2
            (foo2 baz0 baz0)
            (foo2 baz0 baz0)))
t1 =
    (foo2
        (foo2
            (foo2 baz0 baz0)
            (foo2 baz0 baz0))
        (foo2
            (foo2 baz0 baz0)
            (foo2 baz0 (s "bar" []))))

main :: IO ()
main = do
    test0
    runCriterionTests t0 t1

----------------------------------------------------------------
----------------------------------------------------------- fin.
