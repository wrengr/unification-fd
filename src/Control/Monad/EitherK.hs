
{-# LANGUAGE CPP
           , Rank2Types
           , MultiParamTypeClasses
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

----------------------------------------------------------------
--                                                  ~ 2011.06.28
-- |
-- Module      :  Control.Monad.EitherK
-- License     :  A simple permissive license
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  stable
-- Portability :  semi-portable (CPP, Rank2Types, MPTCs, FlexibleInstances)
--
-- A continuation-passing variant of 'Either' for short-circuiting
-- at failure. This code is based on "Control.Monad.MaybeK" and
-- is released under the same simple permissive license
-- (<http://www.haskell.org/haskellwiki/HaskellWiki:Copyrights>).
----------------------------------------------------------------
module Control.Monad.EitherK
    (
    -- * The short-circuiting monad
      EitherK()
    , runEitherK
    , toEitherK
    , throwEitherK
    , catchEitherK
    , eitherK
    -- * The short-circuiting monad transformer
    , EitherKT()
    , runEitherKT
    , toEitherKT
    , liftEitherK
    , lowerEitherK
    , throwEitherKT
    , catchEitherKT
    ) where

import Data.Monoid         (Monoid(..))
import Control.Monad       (MonadPlus(..), liftM)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Error (MonadError(..))

#ifdef __APPLICATIVE_IN_BASE__
import Control.Monad       (ap)
import Control.Applicative (Applicative(..), Alternative(..))
#endif
----------------------------------------------------------------

-- | A continuation-passing encoding of 'Either' as an error monad;
-- also known as @Codensity (Either e)@, if you're familiar with
-- that terminology.
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
-- denote ``errors'' per se. This could also denote computations
-- which short-circuit with the final answer, or similar methods
-- of non-local control flow.
--
-- N.B., the 'Alternative' and 'MonadPlus' instances are left-biased
-- in @a@ and monoidal in @e@. Thus, they are not commutative.
newtype EitherK e a = EK (forall r. (a -> Either e r) -> Either e r)


-- | Execute an @EitherK@ and return the concrete @Either@ encoding.
runEitherK :: EitherK e a -> Either e a
runEitherK (EK m) = m Right
{-# INLINE runEitherK #-}


-- | Lift an @Either@ into an @EitherK@.
toEitherK :: Either e a -> EitherK e a
toEitherK (Left  e) = throwEitherK e
toEitherK (Right a) = return a
{-# INLINE toEitherK #-}


-- | Throw an error in the @EitherK@ monad.
throwEitherK :: e -> EitherK e a
throwEitherK e = EK (\_ -> Left e)
{-# INLINE throwEitherK #-}


-- | Handle errors in the @EitherK@ monad. N.B., this type is more
-- general than that of 'catchError', allowing the type of the
-- errors to change.
catchEitherK :: EitherK e a -> (e -> EitherK f a) -> EitherK f a
catchEitherK m handler = eitherK handler return m
{-# INLINE catchEitherK #-}


-- | A version of 'either' on @EitherK@, for convenience. N.B.,
-- using this function inserts a case match, reducing the range of
-- short-circuiting.
eitherK :: (e -> b) -> (a -> b) -> EitherK e a -> b
eitherK left right m =
    case runEitherK m of
        Left  e -> left  e
        Right a -> right a
{-# INLINE eitherK #-}


instance Functor (EitherK e) where
    fmap f (EK m) = EK (\k -> m (k . f))

#ifdef __APPLICATIVE_IN_BASE__
instance Applicative (EitherK e) where
    pure  = return
    (<*>) = ap

instance (Monoid e) => Alternative (EitherK e) where
    empty = mzero
    (<|>) = mplus
#endif

instance Monad (EitherK e) where
    return a   = EK (\k -> k a)
    EK m >>= f = EK (\k -> m (\a -> case f a of EK n -> n k))
    -- Using case instead of let seems to improve performance
    -- considerably by removing excessive laziness.

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
runEitherKT :: (Monad m) => EitherKT e m a -> m (Either e a)
runEitherKT (EKT m) = m (return . Right)
{-# INLINE runEitherKT #-}


-- | Lift an @Either@ into an @EitherKT@.
toEitherKT :: (Monad m) => Either e a -> EitherKT e m a
toEitherKT (Left  e) = throwEitherKT e
toEitherKT (Right a) = return a
{-# INLINE toEitherKT #-}


-- TODO: isn't there a better implementation that doesn't lose shortcircuiting?
-- | Lift an @EitherK@ into an @EitherKT@.
liftEitherK :: (Monad m) => EitherK e a -> EitherKT e m a
liftEitherK = toEitherKT . runEitherK
{-# INLINE liftEitherK #-}


-- TODO: is there a better implementation?
-- | Lower an @EitherKT@ into an @EitherK@.
lowerEitherK :: (Monad m) => EitherKT e m a -> m (EitherK e a)
lowerEitherK = liftM toEitherK . runEitherKT
{-# INLINE lowerEitherK #-}


-- | Throw an error in the @EitherKT@ monad.
throwEitherKT :: (Monad m) => e -> EitherKT e m a
throwEitherKT e = EKT (\_ -> return (Left e))
{-# INLINE throwEitherKT #-}


-- | Handle errors in the @EitherKT@ monad. N.B., this type is more
-- general than that of 'catchError', allowing the type of the
-- errors to change.
catchEitherKT
    :: (Monad m)
    => EitherKT e m a -> (e -> EitherKT f m a) -> EitherKT f m a
catchEitherKT m handler = EKT $ \k -> do
    ea <- runEitherKT m
    case ea of
        Left  e -> case handler e of EKT m' -> m' k
        Right a -> k a
{-# INLINE catchEitherKT #-}


instance Functor (EitherKT e m) where
    fmap f (EKT m) = EKT (\k -> m (k . f))

#ifdef __APPLICATIVE_IN_BASE__
instance Applicative (EitherKT e m) where
    pure  = return
    (<*>) = ap

-- TODO: is there any way to define catchEitherKT so it only requires Applicative m?
instance (Monad m, Monoid e) => Alternative (EitherKT e m) where
    empty = mzero
    (<|>) = mplus
#endif

instance Monad (EitherKT e m) where
    return a    = EKT (\k -> k a)
    EKT m >>= f = EKT (\k -> m (\a -> case f a of EKT n -> n k))

instance (Monad m, Monoid e) => MonadPlus (EitherKT e m) where
    mzero       = throwEitherKT mempty
    m `mplus` n = catchEitherKT m (catchEitherKT n . (throwEitherKT .) . mappend)

instance (Monad m) => MonadError e (EitherKT e m) where
    throwError = throwEitherKT
    catchError = catchEitherKT

instance MonadTrans (EitherKT e) where
    lift m = EKT (\k -> m >>= k)

----------------------------------------------------------------
----------------------------------------------------------- fin.
