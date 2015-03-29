-- The MPTCs and FlexibleInstances are only for
-- mtl:Control.Monad.{Error,Except}.MonadError
{-# LANGUAGE CPP, Rank2Types, MultiParamTypeClasses, FlexibleInstances #-}
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
-- Module      :  Control.Monad.EitherK
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  semi-portable (CPP, Rank2Types, MPTCs, FlexibleInstances)
--
-- A continuation-passing variant of 'Either' for short-circuiting
-- at failure. This code is based on "Control.Monad.MaybeK".
----------------------------------------------------------------
module Control.Monad.EitherK
    (
    -- * The short-circuiting monad
      EitherK()
    , runEitherK
    , toEitherK
    , eitherK
    , throwEitherK
    , catchEitherK
    -- * The short-circuiting monad transformer
    , EitherKT()
    , runEitherKT
    , toEitherKT
    , liftEitherK
    , lowerEitherK
    , throwEitherKT
    , catchEitherKT
    ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid          (Monoid(..))
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

-- | A continuation-passing encoding of 'Either' as an error monad;
-- also known as @Codensity (Either e)@, if you're familiar with
-- that terminology. N.B., this is not the 2-continuation implementation
-- based on the Church encoding of @Either@. The latter tends to
-- have worse performance than non-continuation based implementations.
--
-- This is generally more efficient than using @Either@ (or the
-- MTL's @Error@) for two reasons. First is that it right associates
-- all binds, ensuring that bad associativity doesn't artificially
-- introduce midpoints in short-circuiting to the nearest handler.
-- Second is that it removes the need for intermediate case
-- expressions.
--
-- Another benefit over MTL's @Error@ is that it doesn't artificially
-- restrict the error type. In fact, there's no reason why @e@ must
-- denote \"errors\" per se. This could also denote computations
-- which short-circuit with the final answer, or similar methods
-- of non-local control flow.
--
-- N.B., the 'Alternative' and 'MonadPlus' instances are left-biased
-- in @a@ and monoidal in @e@. Thus, they are not commutative.
newtype EitherK e a = EK (forall r. (a -> Either e r) -> Either e r)


-- | Execute an @EitherK@ and return the concrete @Either@ encoding.
runEitherK :: EitherK e a -> Either e a
{-# INLINE runEitherK #-}
runEitherK (EK m) = m Right


-- | Lift an @Either@ into an @EitherK@.
toEitherK :: Either e a -> EitherK e a
{-# INLINE toEitherK #-}
toEitherK (Left  e) = throwEitherK e
toEitherK (Right a) = return a


-- | Throw an error in the @EitherK@ monad. This is identical to
-- 'throwError'.
throwEitherK :: e -> EitherK e a
{-# INLINE throwEitherK #-}
throwEitherK e = EK (\_ -> Left e)


-- | Handle errors in the @EitherK@ monad. N.B., this type is more
-- general than that of 'catchError', allowing the type of the
-- errors to change.
catchEitherK :: EitherK e a -> (e -> EitherK f a) -> EitherK f a
{-# INLINE catchEitherK #-}
catchEitherK m handler = eitherK handler return m


-- | A version of 'either' on @EitherK@, for convenience. N.B.,
-- using this function inserts a case match, reducing the range of
-- short-circuiting.
eitherK :: (e -> b) -> (a -> b) -> EitherK e a -> b
{-# INLINE eitherK #-}
eitherK left right m =
    case runEitherK m of
        Left  e -> left  e
        Right a -> right a


instance Functor (EitherK e) where
    fmap f (EK m) = EK (\k -> m (k . f))

instance Applicative (EitherK e) where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad (EitherK e) where
    return a   = EK (\k -> k a)
    EK m >>= f = EK (\k -> m (\a -> case f a of EK n -> n k))
    -- Using case instead of let seems to improve performance
    -- considerably by removing excessive laziness.

instance (Monoid e) => Alternative (EitherK e) where
    empty = mzero
    (<|>) = mplus

instance (Monoid e) => MonadPlus (EitherK e) where
    mzero       = throwEitherK mempty
    m `mplus` n = catchEitherK m $ \me ->
                  catchEitherK n $ \ne ->
                  throwEitherK   $ me `mappend` ne

instance MonadError e (EitherK e) where
    throwError = throwEitherK
    catchError = catchEitherK

----------------------------------------------------------------
----------------------------------------------------------------

-- | A monad transformer version of 'EitherK'.
newtype EitherKT e m a =
    EKT (forall r. (a -> m (Either e r)) -> m (Either e r))


-- | Execute an @EitherKT@ and return the concrete @Either@ encoding.
runEitherKT :: (Applicative m) => EitherKT e m a -> m (Either e a)
{-# INLINE runEitherKT #-}
runEitherKT (EKT m) = m (pure . Right)


-- | Lift an @Either@ into an @EitherKT@.
toEitherKT :: (Applicative m) => Either e a -> EitherKT e m a
{-# INLINE toEitherKT #-}
toEitherKT (Left  e) = throwEitherKT e
toEitherKT (Right a) = pure a


-- | Lift an @EitherK@ into an @EitherKT@.
liftEitherK :: (Applicative m) => EitherK e a -> EitherKT e m a
{-# INLINE liftEitherK #-}
liftEitherK = toEitherKT . runEitherK
--
-- With the above implementation, when @liftEitherK x@ is forced
-- it will force not only @x = EK m@, but will also force @m@. If
-- we want to force only @x@ and to defer @m@, then we should use
-- the following implementation instead:
--
-- > liftEitherK (EK m) = EKT (\k -> either (return . Left) k (m Right))
--
-- Or if we want to defer both @m@ and @x@, then we could use:
--
-- > liftEitherK x = EKT (\k -> either (return . Left) k (runEitherK x))
--
-- However, all versions need to reify @m@ at some point, and
-- therefore will lose short-circuiting. This is necessary since
-- given some @k :: a -> m (Either e r)@ we have no way of constructing
-- the needed @k' :: a -> Either e r@ from it without prematurely
-- executing the side-effects.


-- | Lower an @EitherKT@ into an @EitherK@.
lowerEitherK :: (Applicative m) => EitherKT e m a -> m (EitherK e a)
{-# INLINE lowerEitherK #-}
lowerEitherK = fmap toEitherK . runEitherKT


-- | Throw an error in the @EitherKT@ monad. This is identical to
-- 'throwError'.
throwEitherKT :: (Applicative m) => e -> EitherKT e m a
{-# INLINE throwEitherKT #-}
throwEitherKT e = EKT (\_ -> pure (Left e))


-- | Handle errors in the @EitherKT@ monad. N.B., this type is more
-- general than that of 'catchError', allowing the type of the
-- errors to change.
catchEitherKT
    :: (Applicative m, Monad m)
    => EitherKT e m a -> (e -> EitherKT f m a) -> EitherKT f m a
{-# INLINE catchEitherKT #-}
catchEitherKT m handler = EKT $ \k -> do
    ea <- runEitherKT m
    case ea of
        Left  e -> case handler e of EKT m' -> m' k
        Right a -> k a


instance Functor (EitherKT e m) where
    fmap f (EKT m) = EKT (\k -> m (k . f))

instance Applicative (EitherKT e m) where
    pure   = return
    (<*>)  = ap
    (*>)   = (>>)
    x <* y = x >>= \a -> y >> return a

instance Monad (EitherKT e m) where
    return a    = EKT (\k -> k a)
    EKT m >>= f = EKT (\k -> m (\a -> case f a of EKT n -> n k))

-- In order to define a @(<|>)@ which only requires @Applicative
-- m@ we'd need a law @m (Either e a) -> Either (m e) (m a)@; or
-- equivalently, we'd need to use a 2-CPS style.
instance (Applicative m, Monad m, Monoid e) => Alternative (EitherKT e m) where
    empty = mzero
    (<|>) = mplus

instance (Applicative m, Monad m, Monoid e) => MonadPlus (EitherKT e m) where
    mzero       = throwEitherKT mempty
    m `mplus` n = catchEitherKT m (catchEitherKT n . (throwEitherKT .) . mappend)

instance (Applicative m, Monad m) => MonadError e (EitherKT e m) where
    throwError = throwEitherKT
    catchError = catchEitherKT

instance MonadTrans (EitherKT e) where
    lift m = EKT (\k -> m >>= k)

----------------------------------------------------------------
----------------------------------------------------------- fin.
