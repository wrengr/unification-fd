{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-name-shadowing #-}
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
import Data.Foldable
import Data.Traversable
import Data.List.Extras.Pair
import Control.Applicative
import Control.Monad             (MonadPlus(..))
import Control.Monad.Trans       (MonadTrans(..))
import Control.Monad.Identity    (Identity(..))
import Control.Monad.MaybeK      (MaybeKT, runMaybeKT)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Unification
import Control.Unification.IntVar
----------------------------------------------------------------
----------------------------------------------------------------

equalsMaybeKT, equalsMaybeT, equalsMaybe, equalsBool
    :: (BindingMonad t v m)
    => MutTerm t v  -- ^
    -> MutTerm t v  -- ^
    -> m Bool       -- ^

equalsMaybeKT tl0 tr0 = do
    mb <- runMaybeKT (loop tl0 tr0)
    case mb of
        Nothing -> return False
        Just () -> return True
    where
    loop tl0 tr0 = do
        tl0 <- lift $ semiprune tl0
        tr0 <- lift $ semiprune tr0
        case (tl0, tr0) of
            (MutVar vl, MutVar vr)
                | vl `eqVar` vr -> return () -- success
                | otherwise       -> do
                    mtl <- lift $ lookupVar vl
                    mtr <- lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> mzero
                        (Nothing, Just _ ) -> mzero
                        (Just _,  Nothing) -> mzero
                        (Just tl, Just tr) -> loop tl tr -- TODO: should just jump to match
            (MutVar  _,  MutTerm _ ) -> mzero
            (MutTerm _,  MutVar  _ ) -> mzero
            (MutTerm tl, MutTerm tr) ->
                case zipMatch tl tr of
                Nothing  -> mzero
                Just tlr -> mapM_ (uncurry loop) tlr

equalsMaybeT tl0 tr0 = do
    mb <- runMaybeT (loop tl0 tr0)
    case mb of
        Nothing -> return False
        Just () -> return True
    where
    loop tl0 tr0 = do
        tl0 <- lift $ semiprune tl0
        tr0 <- lift $ semiprune tr0
        case (tl0, tr0) of
            (MutVar vl, MutVar vr)
                | vl `eqVar` vr -> return () -- success
                | otherwise       -> do
                    mtl <- lift $ lookupVar vl
                    mtr <- lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> mzero
                        (Nothing, Just _ ) -> mzero
                        (Just _,  Nothing) -> mzero
                        (Just tl, Just tr) -> loop tl tr -- TODO: should just jump to match
            (MutVar  _,  MutTerm _ ) -> mzero
            (MutTerm _,  MutVar  _ ) -> mzero
            (MutTerm tl, MutTerm tr) ->
                case zipMatch tl tr of
                Nothing  -> mzero
                Just tlr -> mapM_ (uncurry loop) tlr

equalsMaybe tl0 tr0 = do
    mb <- loop tl0 tr0
    case mb of
        Nothing -> return False
        Just () -> return True
    where
    loop tl0 tr0 = do
        tl0 <- semiprune tl0
        tr0 <- semiprune tr0
        case (tl0, tr0) of
            (MutVar vl, MutVar vr)
                | vl `eqVar` vr -> return (Just ()) -- success
                | otherwise     -> do
                    mtl <- lookupVar vl
                    mtr <- lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> return Nothing
                        (Nothing, Just _ ) -> return Nothing
                        (Just _,  Nothing) -> return Nothing
                        (Just tl, Just tr) -> loop tl tr -- TODO: should just jump to match
            (MutVar  _,  MutTerm _  ) -> return Nothing
            (MutTerm _,  MutVar  _  ) -> return Nothing
            (MutTerm tl, MutTerm tr) ->
                case zipMatch tl tr of
                Nothing  -> return Nothing
                Just tlr ->
                    foldr 
                        (\ (tl',tr') k mb ->
                            case mb of
                            Nothing -> return Nothing
                            Just () -> loop tl' tr' >>= k)
                        return
                        tlr
                        (Just ())

{-
foldlM :: (Foldable t, Monad m) => (a -> b -> m a) -> a -> t b -> m a
foldlM f z0 xs = foldr f' return xs z0 where f' x k z = f z x >>= k

mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f = foldr ((>>) . f) (return ())
-}

equalsBool tl0 tr0 = do
    tl0 <- semiprune tl0
    tr0 <- semiprune tr0
    case (tl0, tr0) of
        (MutVar vl, MutVar vr)
            | vl `eqVar` vr -> return True -- success
            | otherwise     -> do
                mtl <- lookupVar vl
                mtr <- lookupVar vr
                case (mtl, mtr) of
                    (Nothing, Nothing) -> return False
                    (Nothing, Just _ ) -> return False
                    (Just _,  Nothing) -> return False
                    (Just tl, Just tr) -> equalsBool tl tr -- TODO: should just jump to match
        (MutVar  _,  MutTerm _  ) -> return False
        (MutTerm _,  MutVar  _  ) -> return False
        (MutTerm tl, MutTerm tr) ->
            case zipMatch tl tr of
            Nothing  -> return False
            Just tlr ->
                -- and <$> mapM (uncurry equalsBool) tlr -- TODO: use foldlM
                -- {-
                foldlM
                    (\b (tl',tr') ->
                        if b
                        then equalsBool tl' tr'
                        else return False)
                    True
                    tlr
                {-
                -- WTF: if we use this implementation instead, then the MaybeT implementation suddenly becomes faster than the Maybe version! (And this function becomes slightly faster too).
                foldr 
                    (\ (tl',tr') k b ->
                        if b
                        then equalsBool tl' tr' >>= k
                        else return False)
                    return
                    tlr
                    True
                -- -}
----------------------------------------------------------------


data S a = S {-# UNPACK #-} !Int ![a]
    deriving (Read, Show, Eq, Ord, Functor, Foldable, Traversable)

instance Unifiable S where
    zipMatch (S a xs) (S b ys)
        | a == b    = fmap (S a) (pair xs ys)
        | otherwise = Nothing

type STerm = MutTerm S IntVar

s :: Int -> [STerm] -> STerm
s = (MutTerm .) . S

foo2 :: STerm -> STerm -> STerm
foo2 x y = s 1 [x,y]

bar0 = s 2 []
baz0 = s 3 []

foo4 :: STerm -> STerm -> STerm -> STerm -> STerm
foo4 a b c d = foo2 (foo2 a b) (foo2 c d)

foo16 a b c d =
    foo4 (foo4 a a a a) (foo4 a a a b) (foo4 a a a c) (foo4 a a a d)

-- N.B., don't go deeper than about 15 if you're printing the term.
fooN :: Int -> STerm
fooN n
    | n <= 0    = baz0
    | otherwise = let t = fooN $! n-1 in foo2 t t

evalIB = runIdentity . evalIntBindingT

main :: IO ()
main =
    let f t = foo2 (foo2 (foo2 baz0 baz0) (foo2 baz0 baz0))
                   (foo2 (foo2 baz0 baz0) (foo2 baz0 t))
        g t = foo2 (foo2 (foo2 baz0 baz0) (foo2 baz0 t))
                   (foo2 (foo2 baz0 baz0) (foo2 baz0 baz0))
        f1z = f baz0; f1r = f bar0; g1z = g baz0; g1r = g bar0
        f2z = f f1z;  f2r = f f1r;  g2z = g g1z;  g2r = g g1r
        f3z = f f2z;  f3r = f f2r;  g3z = g g2z;  g3r = g g2r
        f4z = f f3z;  f4r = f f3r;  g4z = g g3z;  g4r = g g3r
        
        mkBGroup tl tr =
            [ bench "equalsMaybeKT" $ nf (evalIB . equalsMaybeKT tl) tr
            , bench "equalsMaybeT"  $ nf (evalIB . equalsMaybeT  tl) tr
            , bench "equalsMaybe"   $ nf (evalIB . equalsMaybe   tl) tr
            , bench "equalsBool"    $ nf (evalIB . equalsBool    tl) tr
            , bench "equals (lib)"  $ nf (evalIB . equals        tl) tr
            ]
        
        
        xxx = fooN 10
        x0 = foo16 xxx  xxx  xxx  xxx
        xA = foo16 bar0 xxx  xxx  xxx
        xB = foo16 xxx  bar0 xxx  xxx
        xC = foo16 xxx  xxx  bar0 xxx
        xD = foo16 xxx  xxx  xxx  bar0
    in
    defaultMain
        {-
        [ bgroup "x0.xA" $ mkBGroup x0 xA
        , bgroup "x0.xB" $ mkBGroup x0 xB
        , bgroup "x0.xC" $ mkBGroup x0 xC
        , bgroup "x0.xD" $ mkBGroup x0 xD
        , bgroup "x0.x0" $ mkBGroup x0 x0
        ]
        -}
        [ bgroup "g1zr" $ mkBGroup g1z g1r
        , bgroup "g2zr" $ mkBGroup g2z g2r
        , bgroup "g3zr" $ mkBGroup g3z g3r
        , bgroup "g4zr" $ mkBGroup g4z g4r
        --
        , bgroup "f1zr" $ mkBGroup f1z f1r
        , bgroup "f2zr" $ mkBGroup f2z f2r
        , bgroup "f3zr" $ mkBGroup f3z f3r
        , bgroup "f4zr" $ mkBGroup f4z f4r
        --
        , bgroup "f1zz" $ mkBGroup f1z f1z
        , bgroup "f2zz" $ mkBGroup f2z f2z
        , bgroup "f3zz" $ mkBGroup f3z f3z
        , bgroup "f4zz" $ mkBGroup f4z f4z
        ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
