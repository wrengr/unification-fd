-- The MPTCs is only for mtl:Control.Monad.Error.MonadError
{-# LANGUAGE CPP, Rank2Types, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

-- HACK: in GHC 7.10, Haddock complains about unused imports; but,
-- if we use CPP to avoid including them under Haddock, then it
-- will fail!
#ifdef __HADDOCK__
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#endif

----------------------------------------------------------------
--                                                  ~ 2015.03.29
-- |
-- Module      :  Control.Monad.MaybeK
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  semi-portable (CPP, Rank2Types, MPTCs)
--
-- A continuation-passing variant of 'Maybe' for short-circuiting
-- at failure. This is based largely on code from the Haskell Wiki
-- (<http://www.haskell.org/haskellwiki/Performance/Monads>) which
-- was released under a simple permissive license
-- (<http://www.haskell.org/haskellwiki/HaskellWiki:Copyrights>).
-- However, various changes and extensions have been made, which
-- are subject to the BSD license of this package.
----------------------------------------------------------------
module Control.Monad.MaybeK
    (
    -- * The partiality monad
      MaybeK
    , runMaybeK
    , toMaybeK
    , maybeK
    -- * The partiality monad transformer
    , MaybeKT
    , runMaybeKT
    , toMaybeKT
    , liftMaybeK
    , lowerMaybeK
    ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative  (Applicative(..))
#endif
import Control.Applicative  (Alternative(..))
import Control.Monad        (MonadPlus(..), ap)
import Control.Monad.Trans  (MonadTrans(..))
#if (MIN_VERSION_mtl(2,2,1))
-- aka: transformers(0,4,1)
import Control.Monad.Except (MonadError(..))
#else
import Control.Monad.Error  (MonadError(..))
#endif
----------------------------------------------------------------
----------------------------------------------------------------

-- | A continuation-passing encoding of 'Maybe'; also known as
-- @Codensity Maybe@, if you're familiar with that terminology.
-- N.B., this is not the 2-continuation implementation based on the
-- Church encoding of @Maybe@. The latter tends to have worse
-- performance than non-continuation based implementations.
--
-- This is generally more efficient than using @Maybe@ for two
-- reasons. First is that it right associates all binds, ensuring
-- that bad associativity doesn't artificially introduce midpoints
-- in short-circuiting to the nearest handler. Second is that it
-- removes the need for intermediate case expressions.
--
-- N.B., the 'Alternative' and 'MonadPlus' instances are left-biased
-- in @a@. Thus, they are not commutative.
newtype MaybeK a = MK (forall r. (a -> Maybe r) -> Maybe r)


-- | Execute the @MaybeK@ and return the concrete @Maybe@ encoding.
runMaybeK :: MaybeK a -> Maybe a
{-# INLINE runMaybeK #-}
runMaybeK (MK m) = m return


-- | Lift a @Maybe@ into @MaybeK@.
toMaybeK :: Maybe a -> MaybeK a
{-# INLINE toMaybeK #-}
toMaybeK Nothing  = mzero
toMaybeK (Just a) = return a


-- | A version of 'maybe' for convenience. This is almost identical
-- to 'mplus' but allows applying a continuation to @Just@ values
-- as well as handling @Nothing@ errors. If you only want to handle
-- the errors, use 'mplus' instead.
maybeK :: b -> (a -> b) -> MaybeK a -> b
{-# INLINE maybeK #-}
maybeK nothing just m =
    case runMaybeK m of
    Nothing -> nothing
    Just a  -> just a


instance Functor MaybeK where
    fmap f (MK m) = MK (\k -> m (k . f))

instance Applicative MaybeK where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad MaybeK where
    return a   = MK (\k -> k a)
    MK m >>= f = MK (\k -> m (\a -> case f a of MK n -> n k))
    -- Using case instead of let seems to improve performance
    -- considerably by removing excessive laziness.

-- This is non-commutative, but it's the same as Alternative Maybe.
instance Alternative MaybeK where
    empty = mzero
    (<|>) = mplus

instance MonadPlus MaybeK where
    mzero       = MK (\_ -> Nothing)
    m `mplus` n = maybeK n return m

instance MonadError () MaybeK where
    throwError _   = mzero
    catchError m f = maybeK (f ()) return m

----------------------------------------------------------------

-- | A monad transformer version of 'MaybeK'.
newtype MaybeKT m a = MKT (forall r . (a -> m (Maybe r)) -> m (Maybe r))


-- | Execute a @MaybeKT@ and return the concrete @Maybe@ encoding.
runMaybeKT :: (Applicative m) => MaybeKT m a -> m (Maybe a)
{-# INLINE runMaybeKT #-}
runMaybeKT (MKT m) = m (pure . Just)


-- | Lift a @Maybe@ into an @MaybeKT@.
toMaybeKT :: (Applicative m) => Maybe a -> MaybeKT m a
{-# INLINE toMaybeKT #-}
toMaybeKT Nothing  = MKT (\_ -> pure Nothing)
toMaybeKT (Just a) = pure a


-- | Lift an @MaybeK@ into an @MaybeKT@.
liftMaybeK :: (Applicative m) => MaybeK a -> MaybeKT m a
{-# INLINE liftMaybeK #-}
liftMaybeK = toMaybeKT . runMaybeK
--
-- With the above implementation, when @liftMaybeK x@ is forced it
-- will force not only @x = MK m@, but will also force @m@. If we
-- want to force only @x@ and to defer @m@, then we should use the
-- following implementation instead:
--
-- > liftMaybeK (MK m) = MKT (\k -> maybe (return Nothing) k (m Just))
--
-- Or if we want to defer both @m@ and @x@, then we could use:
--
-- > liftMaybeK x = MKT (\k -> maybe (return Nothing) k (runMaybeK x))
--
-- However, all versions need to reify @m@ at some point, and
-- therefore will lose short-circuiting. This is necessary since
-- given some @k :: a -> m (Maybe r)@ we have no way of constructing
-- the needed @k' :: a -> Maybe r@ from it without prematurely
-- executing the side-effects.


-- | Lower an @MaybeKT@ into an @MaybeK@.
lowerMaybeK :: (Applicative m) => MaybeKT m a -> m (MaybeK a)
{-# INLINE lowerMaybeK #-}
lowerMaybeK = fmap toMaybeK . runMaybeKT


instance Functor (MaybeKT m) where
    fmap f (MKT m) = MKT (\k -> m (k . f))

instance Applicative (MaybeKT m) where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad (MaybeKT m) where
    return a    = MKT (\k -> k a)
    MKT m >>= f = MKT (\k -> m (\a -> case f a of MKT n -> n k))

-- In order to define a @(<|>)@ which only requires @Applicative
-- m@ we'd need a law @m (Either e a) -> Either (m e) (m a)@; or
-- equivalently, we'd need to use a 2-CPS style.
instance (Applicative m, Monad m) => Alternative (MaybeKT m) where
    empty = mzero
    (<|>) = mplus

instance (Applicative m, Monad m) => MonadPlus (MaybeKT m) where
    mzero = MKT (\_ -> return Nothing)
    
    m `mplus` n = MKT $ \k -> do
        mb <- runMaybeKT m
        case mb of
            Nothing -> case n of MKT n' -> n' k
            Just a  -> k a

instance (Applicative m, Monad m) => MonadError () (MaybeKT m) where
    throwError _   = mzero
    catchError m f = MKT $ \k -> do
        mb <- runMaybeKT m
        case mb of
            Nothing -> case f () of MKT n -> n k
            Just a  -> k a

instance MonadTrans MaybeKT where
    lift m = MKT (\k -> m >>= k)

----------------------------------------------------------------
----------------------------------------------------------- fin.
