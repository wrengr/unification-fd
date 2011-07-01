-- The MPTCs is only for mtl:Control.Monad.Error.MonadError
{-# LANGUAGE Rank2Types, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                  ~ 2011.06.30
-- |
-- Module      :  Control.Monad.MaybeK
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  semi-portable (Rank2Types, MPTCs)
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

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad       (MonadPlus(..), liftM, ap)
import Control.Monad.Error (MonadError(..))
import Control.Monad.Trans (MonadTrans(..))
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
runMaybeK (MK m) = m return
{-# INLINE runMaybeK #-}


-- | Lift a @Maybe@ into @MaybeK@.
toMaybeK :: Maybe a -> MaybeK a
toMaybeK Nothing  = mzero
toMaybeK (Just a) = return a
{-# INLINE toMaybeK #-}


-- | A version of 'maybe' for convenience. This is almost identical
-- to 'mplus' but allows applying a continuation to @Just@ values
-- as well as handling @Nothing@ errors. If you only want to handle
-- the errors, use 'mplus' instead.
maybeK :: b -> (a -> b) -> MaybeK a -> b
maybeK nothing just m =
    case runMaybeK m of
    Nothing -> nothing
    Just a  -> just a
{-# INLINE maybeK #-}


instance Functor MaybeK where
    fmap f (MK m) = MK (\k -> m (k . f))

instance Applicative MaybeK where
    pure  = return
    (<*>) = ap

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
runMaybeKT :: (Monad m) => MaybeKT m a -> m (Maybe a)
runMaybeKT (MKT m) = m (return . Just)
{-# INLINE runMaybeKT #-}


-- | Lift a @Maybe@ into an @MaybeKT@.
toMaybeKT :: (Monad m) => Maybe a -> MaybeKT m a
toMaybeKT Nothing  = mzero
toMaybeKT (Just a) = return a
{-# INLINE toMaybeKT #-}


-- TODO: isn't there a better implementation that doesn't lose shortcircuiting?
-- | Lift an @MaybeK@ into an @MaybeKT@.
liftMaybeK :: (Monad m) => MaybeK a -> MaybeKT m a
liftMaybeK = toMaybeKT . runMaybeK
{-# INLINE liftMaybeK #-}


-- TODO: is there a better implementation?
-- | Lower an @MaybeKT@ into an @MaybeK@.
lowerMaybeK :: (Monad m) => MaybeKT m a -> m (MaybeK a)
lowerMaybeK = liftM toMaybeK . runMaybeKT
{-# INLINE lowerMaybeK #-}


instance Functor (MaybeKT m) where
    fmap f (MKT m) = MKT (\k -> m (k . f))

instance Applicative (MaybeKT m) where
    pure  = return
    (<*>) = ap

instance Monad (MaybeKT m) where
    return a    = MKT (\k -> k a)
    MKT m >>= f = MKT (\k -> m (\a -> case f a of MKT n -> n k))

instance (Monad m) => Alternative (MaybeKT m) where
    empty = mzero
    (<|>) = mplus

instance (Monad m) => MonadPlus (MaybeKT m) where
    mzero = MKT (\_ -> return Nothing)
    
    m `mplus` n = MKT $ \k -> do
        mb <- runMaybeKT m
        case mb of
            Nothing -> case n of MKT n' -> n' k
            Just a  -> k a

instance (Monad m) => MonadError () (MaybeKT m) where
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
