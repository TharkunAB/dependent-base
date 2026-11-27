{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DependentTypes #-}

{- | Propositional equality, congruence, substitution, ASCII equational
reasoning, and the 'Inspect' view idiom.
-}
module Data.Type.Equality.Dependent (
    (:~:) (..),
    (:~~:) (..),
    type (~),
    sym,
    trans,
    cong,
    cong2,
    congApp,
    subst,
    substImplicit,
    rewrite,
    withEquality,
    castWith,
    gcastWith,
    begin,
    stepEq,
    stepRefl,
    (===),
    qed,
    Inspect (..),
    inspect,
    Matchability (..),
    M,
    U,
) where

import Data.Kind (Type)
import Data.Type.Equality (
    castWith,
    gcastWith,
    sym,
    trans,
    (:~:) (..),
    (:~~:) (..),
    type (~),
 )
import GHC.Matchability (M, Matchability (..), U)
import Prelude ()

{- Note [Visible congruence and ASCII equational reasoning]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Function 'cong' binds the type-level function with a visible @forall f ->@
quantifier (GHC Proposal #281) and quantifies over 'Matchability'. Callers pass
ordinary functions, constructors, operator sections, and compositions directly
in term syntax, as in @cong Succ eq@, @cong (plus m) eq@, and
@cong (Succ . plus m) eq@.

Equational reasoning chains use ASCII combinators ('begin', 'stepEq',
'stepRefl', '(===)', and 'qed') to match GHC @base@ conventions without
introducing Unicode operators.
-}

{- | Apply a matchable or unmatchable function to both sides of an equality.
See Note [Visible congruence and ASCII equational reasoning].
-}
cong ::
    forall {a} {b} {m :: Matchability}.
    forall (f :: a %m -> b) ->
    forall (x :: a) (y :: a).
    x :~: y -> f x :~: f y
cong _ Refl = Refl

-- | Apply a binary function to equal arguments in both positions.
cong2 ::
    forall {a} {b} {c} {m1 :: Matchability} {m2 :: Matchability}.
    forall (f :: a %m1 -> b %m2 -> c) ->
    forall (x1 :: a) (y1 :: a) (x2 :: b) (y2 :: b).
    x1 :~: y1 -> x2 :~: y2 -> f x1 x2 :~: f y1 y2
cong2 _ Refl Refl = Refl

-- | Apply equal functions to one shared argument.
congApp ::
    forall {a} {b} {m :: Matchability} {f :: a %m -> b} {g :: a %m -> b} (x :: a).
    f :~: g -> f x :~: g x
congApp Refl = Refl

-- | Transport evidence of @p x@ to @p y@ along an explicit predicate @p@.
subst ::
    forall {k} {m :: Matchability}.
    forall (p :: k %m -> Type) ->
    forall {x :: k} {y :: k}.
    x :~: y -> p x -> p y
subst _ Refl px = px

-- | Transport evidence of @p x@ to @p y@ when @p@ is inferred from context.
substImplicit ::
    forall {k} {m :: Matchability} (p :: k %m -> Type) {x :: k} {y :: k}.
    x :~: y -> p x -> p y
substImplicit Refl px = px

-- | Bring a propositional equality into scope as a nominal constraint.
rewrite :: forall {k} (a :: k) (b :: k) r. (a :~: b) -> ((a ~ b) => r) -> r
rewrite = gcastWith

-- | Alias for 'rewrite'.
withEquality :: forall {k} (a :: k) (b :: k) r. (a :~: b) -> ((a ~ b) => r) -> r
withEquality = gcastWith

-- | Start an ASCII equational reasoning chain.
begin :: forall {k} (x :: k) (y :: k). (x :~: y) -> (x :~: y)
begin eq = eq

infixr 2 `stepEq`

{- | State the intermediate term @y@ via @\@y@ and step from @x@ to @z@ via
@x :~: y@ and @y :~: z@.
-}
stepEq :: forall {k} (y :: k) {x :: k} {z :: k}. (x :~: y) -> (y :~: z) -> (x :~: z)
stepEq xy yz = trans xy yz

{- | State an intermediate term @x@ via @\@x@ that reduces definitionally to the
next step.
-}
stepRefl :: forall {k} (x :: k) (y :: k). (x :~: y) -> (x :~: y)
stepRefl eq = eq

infixr 2 ===

-- | Chain two propositional equality steps in left-to-right order.
(===) :: forall {k} (x :: k) (y :: k) (z :: k). (x :~: y) -> (y :~: z) -> (x :~: z)
(===) = trans

-- | Close an ASCII equational reasoning chain at endpoint @x@.
qed :: forall {k} (x :: k). x :~: x
qed = Refl

{- Note [The Inspect view idiom]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Pattern matching on an intermediate call @case f x of { True -> ... }@ refines
the value of @f x@ at the term level, but an ordinary @case@ scrutinee that is
not a variable or constructor index does not introduce @f x ~ True@ into scope.
Matching on @inspect f x@ returns @Reveal y eq@ where @y :: b@ is a retained
value and @eq :: f x :~: y@ witnesses the equality between the call @f x@ and
the pattern-matched result @y@.
-}

{- | View pairing the runtime result @y@ of @lhs@ with a proof @lhs :~: y@.
See Note [The Inspect view idiom].
-}
data Inspect (lhs :: b) where
    Reveal :: foreach (y :: b) -> (lhs :~: y) -> Inspect lhs

-- | Observe the value of @f x@ together with a propositional proof @f x :~: y@.
inspect :: forall {a} {b}. foreach (f :: a -> b) -> foreach (x :: a) -> Inspect (f x)
inspect f x = Reveal (f x) Refl
