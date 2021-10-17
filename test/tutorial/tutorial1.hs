{-# LANGUAGE DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs
    -fno-warn-deprecations
    -fno-warn-missing-signatures
    -fno-warn-unused-do-bind
    #-}

import Data.List.Extras.Pair  (pairWith)
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad.Error    (ErrorT(..), runErrorT)
import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic    (Logic(), runLogic)
import Control.Monad.Trans    (MonadTrans(lift))
import Control.Unification
import Control.Unification.IntVar

----------------------------------------------------------------
data T a = T String [a]
    deriving (Show, Functor, Foldable, Traversable)

foo x y = UTerm$T "foo" [x,y]
bar     = UTerm$T "bar" []
baz x   = UTerm$T "baz" [x]

atom n  = UTerm$T n []

instance Unifiable T where
    zipMatch (T m ls) (T n rs)
        | m /= n    = Nothing
        | otherwise =
            T n <$> pairWith (\l r -> Right(l,r)) ls rs

----------------------------------------------------------------
-- Some aliases for simplifying type signatures:
type PrologTerm           = UTerm T IntVar
type PrologFailure        = UnificationFailure T IntVar
type PrologBindingState   = IntBindingState T
type FallibleBindingMonad = ErrorT PrologFailure (IntBindingT T Identity)
type PrologMonad          = ErrorT PrologFailure (IntBindingT T Logic)

----------------------------------------------------------------

-- | @example1(X,Y,Z) :- X = Y, Y = Z.@
-- example1 :: PrologTerm -> PrologTerm -> PrologTerm -> Example
example1 x y z = do
    x =:= y
    y =:= z

-- | A more efficient implementation of 'example1'.
-- example1' :: PrologTerm -> PrologTerm -> PrologTerm -> Example
example1' x y z = do
    y' <- x =:= y
    y' =:= z


-- N.B., This type signature is (unfortunately) necessary in order
-- to avoid ambiguity when we discard the variable it returns. But,
-- if you never discard the result, then you should be able to get
-- away with commenting out the signature.
getFreeVar
    :: (Applicative m, Monad m)
    => ErrorT PrologFailure (IntBindingT T m) PrologTerm
getFreeVar = lift (UVar <$> freeVar)


-- | @example2(X,Z) :- X = Y, Y = Z.@
-- example2 :: PrologTerm -> PrologTerm -> Example
example2 x z = do
    y <- getFreeVar
    x =:= y
    y =:= z


-- | @example3(X,Z) :- example1(X,Y,Z).@
-- example3 :: PrologTerm -> PrologTerm -> Example
example3 x z = do
    y <- getFreeVar
    example1 x y z


-- BUG: transformers-0.4.1.0 deprecated Control.Monad.Trans.Error
-- (transformers-0.3.0.0 says it's fine). In order to use
-- Control.Monad.Trans.Except, we need a monoid instance... so we'll
-- need to redefine UnificationFailure to deal with all this
--
-- | @example4(X) :- X = bar; X = backtrack.@
-- example4 :: PrologTerm -> Example
example4 x = (x =:= bar) <|> (x =:= atom "backtrack")


-- However, note that the semantics of 'example4' may not be what
-- is expected. In particular, this example will fail with a
-- @TermMismatch@ because the invocation of 'example4' commits to
-- the success of its first branch, so that by the time we execute
-- the last line of this example, we can't get the 'example4'
-- invocation to backtrack and try the other branch.
commitsTooEarly = do
    x <- getFreeVar
    example4 x
    x =:= atom "backtrack"

{- However, both of these examples work just fine (since the first
-- branch of 'example4' fails immediately). Thus, choice does indeed
-- work, even if backtracking doesn't:

choiceWorks1 = do
    x <- getFreeVar
    x =:= atom "backtrack"
    example4 x

choiceWorks2 = do
    example4 (atom "backtrack")

-}


-- | Note that the semantics of this test may not be what is expected,
-- depending on the exact monad stack used. In particular, for
-- @FallibleBindingMonad@ it does not give Prolog's semantics!
backtrackingTest = do
    x <- getFreeVar
    y <- getFreeVar
    (x =:= y >> failure) <|> return (foo x y)
    where
    failure = atom "a" =:= atom "b"

----------------------------------------------------------------
runFBM
    :: FallibleBindingMonad a
    -> (Either PrologFailure a, PrologBindingState)
runFBM = runIdentity . runIntBindingT . runErrorT

evalFBM :: FallibleBindingMonad a -> Either PrologFailure a
evalFBM = runIdentity . evalIntBindingT . runErrorT

execFBM :: FallibleBindingMonad a -> PrologBindingState
execFBM = runIdentity . execIntBindingT . runErrorT


runProlog
    :: PrologMonad a
    -> Maybe (Either PrologFailure a, PrologBindingState)
runProlog = observeMaybe . runIntBindingT . runErrorT

evalProlog :: PrologMonad a -> Maybe (Either PrologFailure a)
evalProlog = observeMaybe . evalIntBindingT . runErrorT

execProlog :: PrologMonad a -> Maybe PrologBindingState
execProlog = observeMaybe . execIntBindingT . runErrorT

observeMaybe :: Logic a -> Maybe a
observeMaybe mx = runLogic mx (\a _ -> Just a) Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
