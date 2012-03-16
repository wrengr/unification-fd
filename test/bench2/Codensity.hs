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
    where
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

equalsMb tl tr = do
    mb <- runMaybeT (equals_loop tl tr)
    case mb of
        Nothing -> return False
        Just () -> return True
    where
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

-- BUG: this doesn't actually inline/specialize...
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

bar0 :: STerm
bar0 = s "bar" []

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

main :: IO ()
main =
    let f t = foo2 (foo2 (foo2 baz0 baz0) (foo2 baz0 baz0))
                   (foo2 (foo2 baz0 baz0) (foo2 baz0 t))
        t0l = f baz0
        t0r = f bar0
        t1l = f t0l
        t1r = f t0r
        t2l = f t1l
        t2r = f t1r
        t3l = f t2l
        t3r = f t2r
    in
    defaultMain
        [ bgroup "equalsK (False)"
            [ bench "t0" $ nf (evalIntBinding . equalsK t0l) t0r
            , bench "t1" $ nf (evalIntBinding . equalsK t1l) t1r
            , bench "t2" $ nf (evalIntBinding . equalsK t2l) t2r
            , bench "t3" $ nf (evalIntBinding . equalsK t3l) t3r
            ]
        , bgroup "equalsK (True)"
            [ bench "t0" $ nf (evalIntBinding . equalsK t0l) t0l
            , bench "t1" $ nf (evalIntBinding . equalsK t1l) t1l
            , bench "t2" $ nf (evalIntBinding . equalsK t2l) t2l
            , bench "t3" $ nf (evalIntBinding . equalsK t3l) t3l
            ]
        , bgroup "equalsMb (False)"
            [ bench "t0" $ nf (evalIntBinding . equalsMb t0l) t0r
            , bench "t1" $ nf (evalIntBinding . equalsMb t1l) t1r
            , bench "t2" $ nf (evalIntBinding . equalsMb t2l) t2r
            , bench "t3" $ nf (evalIntBinding . equalsMb t3l) t3r
            ]
        , bgroup "equalsMb (True)"
            [ bench "t0" $ nf (evalIntBinding . equalsMb t0l) t0l
            , bench "t1" $ nf (evalIntBinding . equalsMb t1l) t1l
            , bench "t2" $ nf (evalIntBinding . equalsMb t2l) t2l
            , bench "t3" $ nf (evalIntBinding . equalsMb t3l) t3l
            ]
        , bgroup "equalsLib (False)"
            [ bench "t0" $ nf (evalIntBinding . equals t0l) t0r
            , bench "t1" $ nf (evalIntBinding . equals t1l) t1r
            , bench "t2" $ nf (evalIntBinding . equals t2l) t2r
            , bench "t3" $ nf (evalIntBinding . equals t3l) t3r
            ]
        , bgroup "equalsLib (True)"
            [ bench "t0" $ nf (evalIntBinding . equals t0l) t0l
            , bench "t1" $ nf (evalIntBinding . equals t1l) t1l
            , bench "t2" $ nf (evalIntBinding . equals t2l) t2l
            , bench "t3" $ nf (evalIntBinding . equals t3l) t3l
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

----------------------------------------------------------------
----------------------------------------------------------- fin.
