
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.06.28
-- |
-- Module      :  Control.Monad.BacktrackST
-- Copyright   :  Copyright (c) 2008--2011 wren ng thornton
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  maybe semi-portable (RankNTypes)
--
-- This module defines a variant of the ST monad which supports
-- backtracking via logging all writes to variables.
----------------------------------------------------------------
module Control.Monad.BacktrackST
    (
    -- * Backtracking references for 'BacktrackST'
      BSTRef()
    , newBSTRef
    , readBSTRef
    , writeBSTRef
    -- * Backtracking ST monad
    , BacktrackST()
    , runBST
    , liftST
    ) where

import Data.STRef
import Data.Monoid
import Control.Monad       (MonadPlus(..), ap)
import Control.Monad.ST
import Control.Applicative (Applicative(..), Alternative(..))
----------------------------------------------------------------
----------------------------------------------------------------

-- STLog s ~ Done | UnWrite (STRef s a) a (STLog s)
--
-- N.B., we store the list in reverse order, so that undoSTLog
-- doesn't build up a deep stack (because we care about undoSTLog
-- more than redoSTLog). Hence, mappend should always be called
-- with arguments in the opposite order they were evaluated in.
newtype STLog s =
    STLog (forall r. r -> (forall a. STRef s a -> a -> r -> r) -> r)


nilSTL :: STLog s
nilSTL = STLog const


consSTL :: STRef s a -> a -> STLog s -> STLog s
consSTL r x (STLog k) = STLog $ \n c -> c r x (k n c)


{-
snocSTL :: STLog s -> STRef s a -> a -> STLog s
snocSTL (STLog k) r x = STLog $ \n c -> k (c r x n) c
-}


instance Monoid (STLog s) where
    mempty = nilSTL
    mappend (STLog kl) (STLog kr) = STLog $ \n c -> kl (kr n c) c


-- | Write the old values back into memory from the log, undoing
-- the side-effects of an ST action.
undoSTLog :: STLog s -> ST s ()
undoSTLog (STLog k) = k (return ()) (\r x xs -> writeSTRef r x >> xs)


{-
-- This will work if we also track the new value in writeBSTRef.
-- | Write the new values back into memory from the log, replaying
-- (part of) an ST action. This only replays the side-effects as
-- they occured the first time, it doesn't replay the whole ST
-- action, which may have made choices depending on part of the
-- environment not captured in the log.
redoSTLog :: STLog s -> ST s ()
redoSTLog (STLog k) = k (return ()) (\r x x' xs -> xs >> writeSTRef r x')
-}

----------------------------------------------------------------

-- | A mutable reference in the 'BacktrackST' monad.
newtype BSTRef s a = BSTRef (STRef s a)


newBSTRef :: a -> BacktrackST s (BSTRef s a)
newBSTRef x = BST $ do
    r <- newSTRef x
    return (nilSTL, Just (BSTRef r))


readBSTRef :: BSTRef s a -> BacktrackST s a
readBSTRef (BSTRef r) = BST $ do
    x <- readSTRef r
    return (nilSTL, Just x)


writeBSTRef :: BSTRef s a -> a -> BacktrackST s ()
writeBSTRef (BSTRef r) x' = BST $ do
    x <- readSTRef r
    writeSTRef r x'
    return (consSTL r x nilSTL, Just ())


{-
-- Don't write now, instead write while backtracking. This is proof
-- that we shouldn't let clients access the log, lest they do odd
-- things.
writeOnFail :: BSTRef s a -> a -> BacktrackST s ()
writeOnFail (BSTRef r) x' = BST $ do
    return (consSTL r x' nilSTL, Just ())
-}

----------------------------------------------------------------
-- BacktrackST s ~ MaybeT (WriterT (STLog s) (ST s))
-- | The backtracking 'ST' monad. In order to support backtracking we log all writes so that we can revert them. Unfortunately, as it stands, the logging is incredibly naive and prone to space leaks. This will be corrected in the future.
newtype BacktrackST s a = BST { unBST :: ST s (STLog s, Maybe a) }
-- BUG: Fix it!
-- (1) only log when necessary
-- (2) perform log compaction to avoid redundant writes
-- (3) I'm sure there are other major issues


runBST :: (forall s. BacktrackST s a) -> Maybe a
runBST m = runST (snd `fmap` unBST m)


-- | Lift a raw @ST@ computation into @BacktrackST@. The raw @ST@
-- action can manipulate 'STRef's without logging, but it cannot
-- access 'BSTRef's since we would not know how to undo the changes.
liftST :: ST s a -> BacktrackST s a
liftST = BST . fmap ((,) nilSTL . Just)


instance Functor (BacktrackST s) where
    fmap f = BST . fmap (fmap (fmap f)) . unBST

instance Applicative (BacktrackST s) where
    pure  = return
    (<*>) = ap

instance Alternative (BacktrackST s) where
    empty = mzero
    (<|>) = mplus

instance Monad (BacktrackST s) where
    return = BST . return . (,) nilSTL . Just
    
    BST mx >>= f = BST $ do
        (qx,x) <- mx
        case x of
            Nothing -> return (qx,Nothing)
            Just x' -> do
                (qy,y) <- unBST $ f x'
                return (qy `mappend` qx, y)

instance MonadPlus (BacktrackST s) where
    mzero = BST $ return (nilSTL, Nothing)
    
    BST ml `mplus` BST mr = BST $ do
        (ql,l) <- ml
        case l of
            Nothing -> undoSTLog ql >> mr
            Just _  -> return (ql,l)

----------------------------------------------------------------
----------------------------------------------------------- fin.
