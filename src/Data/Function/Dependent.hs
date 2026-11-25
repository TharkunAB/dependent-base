{-# LANGUAGE DependentTypes #-}

-- | Dependent and matchability-polymorphic function combinators.
module Data.Function.Dependent
  ( (.)
  , composeDep
  , composeSigma
  , ($)
  , applyDep
  , id
  , idDep
  , const
  , constDep
  , flip
  , flipDep
  , on
  ) where

import Data.Kind (Type)
import GHC.Matchability (Matchability, U)
import GHC.Sigma (Sigma (Pair))
import Prelude (const, flip, id)

{- Note [First-class dependent function composition]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Function '(.)' generalizes 'Prelude.(.)' to dependent consumers whose result
type mentions the intermediate value @f x@:

  (.) :: forall {a} {b} {m :: Matchability} (c :: b %m -> Type).
         (foreach (y :: b) -> c y)
      -> foreach (f :: a -> b)
      -> foreach (x :: a)
      -> c (f x)

When the first argument @g@ is a dependent function @foreach (y :: b) -> Body@,
GHC synthesizes the motive @\y -> Body@ automatically so compound equality
targets such as @plusIdentityR . Succ@ and @plusIdentityR . plus 1@ require no
helper type synonym. When @g :: b -> d@ is an ordinary non-dependent function,
GHC instantiates @c@ with the constant family @\y -> d@ and casts the vacuous
@foreach@ binders to ordinary arrows without eta-expanding @g@ or @f@.

GHC recognizes the canonical signature of '(.)' so local @let@/@where@ aliases
@to = h . f@ and inline retained function arguments @MkIso (h . f) (g . k)@
lower to the certified composition source table.
-}

infixr 9 .

-- | Compose a dependent or ordinary consumer with an ordinary function.
-- See Note [First-class dependent function composition].
(.) :: forall {a} {b} {m :: Matchability} (c :: b %m -> Type).
       (foreach (y :: b) -> c y)
    -> foreach (f :: a -> b)
    -> foreach (x :: a)
    -> c (f x)
(g . f) x = g (f x)

-- | Compose an indexed binary consumer with a dependent producer over one
-- shared runtime input.
composeDep
  :: forall {a} {mb :: Matchability} {b :: a %mb -> Type}
            {mc :: Matchability} (c :: a %mc -> Type).
     (foreach (x :: a) -> b x -> c x)
  -> (foreach (x :: a) -> b x)
  -> foreach (x :: a)
  -> c x
composeDep g f x = g x (f x)

-- | Pair the input and output of a dependent producer and pass the resulting
-- 'Sigma' package to a consumer.
composeSigma
  :: forall {a} (b :: a %U -> Type) {d}.
     (Sigma a b -> d)
  -> (foreach (x :: a) -> b x)
  -> foreach (x :: a)
  -> d
composeSigma g f x = g (Pair x (f x))

infixr 0 $

-- | Apply a dependent or ordinary function to an argument at low fixity.
($) :: forall {a} {m :: Matchability} (b :: a %m -> Type).
       (foreach (x :: a) -> b x)
    -> foreach (x :: a)
    -> b x
f $ x = f x

-- | Named synonym for dependent application '($)'.
applyDep
  :: forall {a} {m :: Matchability} (b :: a %m -> Type).
     (foreach (x :: a) -> b x)
  -> foreach (x :: a)
  -> b x
applyDep f x = f x

-- | Return a retained argument unchanged.
idDep :: forall {a}. foreach (x :: a) -> a
idDep x = x

-- | Return the first argument and ignore a retained second argument.
constDep :: forall {a} {b}. a -> foreach (y :: b) -> a
constDep x _ = x

-- | Swap the two retained arguments of a binary dependent function.
flipDep
  :: forall {a} {b} {m :: Matchability} (c :: a %U -> b %m -> Type).
     (foreach (x :: a) -> foreach (y :: b) -> c x y)
  -> foreach (y :: b)
  -> foreach (x :: a)
  -> c x y
flipDep f y x = f x y

infixl 0 `on`

-- | Combine two inputs after projecting both through one function.
on :: forall a b c. (b -> b -> c) -> (a -> b) -> a -> a -> c
on combine project x y = combine (project x) (project y)
{-# INLINE on #-}
