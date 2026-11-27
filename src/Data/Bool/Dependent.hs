{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Certified total Boolean operations and fundamental algebraic laws.
module Data.Bool.Dependent (
    Bool (..),
    not,
    (&&),
    (||),
    otherwise,
    bool,
    notInvolutive,
    andTrueL,
    andTrueR,
    andFalseR,
    orFalseL,
    orFalseR,
    orTrueR,
    andAssoc,
    orAssoc,
    andComm,
    orComm,
    deMorganAnd,
    deMorganOr,
) where

import Data.Bool (Bool (..), not, otherwise, (&&), (||))
import Data.Type.Equality ((:~:) (Refl))
import Prelude ()

{- | Case analysis on a 'Bool': return the first value for 'False' and the
second value for 'True'.
-}
bool :: forall a. a -> a -> Bool -> a
bool f _ False = f
bool _ t True = t

-- | Double negation returns the original 'Bool'.
notInvolutive :: foreach (b :: Bool) -> not (not b) :~: b
notInvolutive False = Refl
notInvolutive True = Refl

-- | Left identity of '(&&)'.
andTrueL :: foreach (b :: Bool) -> (True && b) :~: b
andTrueL _ = Refl

-- | Right identity of '(&&)'.
andTrueR :: foreach (b :: Bool) -> (b && True) :~: b
andTrueR False = Refl
andTrueR True = Refl

-- | Right zero of '(&&)'.
andFalseR :: foreach (b :: Bool) -> (b && False) :~: False
andFalseR False = Refl
andFalseR True = Refl

-- | Left identity of '(||)'.
orFalseL :: foreach (b :: Bool) -> (False || b) :~: b
orFalseL _ = Refl

-- | Right identity of '(||)'.
orFalseR :: foreach (b :: Bool) -> (b || False) :~: b
orFalseR False = Refl
orFalseR True = Refl

-- | Right zero of '(||)'.
orTrueR :: foreach (b :: Bool) -> (b || True) :~: True
orTrueR False = Refl
orTrueR True = Refl

-- | Conjunction '(&&)' is associative.
andAssoc ::
    foreach (x :: Bool) ->
    foreach (y :: Bool) ->
    foreach (z :: Bool) ->
    ((x && y) && z) :~: (x && (y && z))
andAssoc False _ _ = Refl
andAssoc True _ _ = Refl

-- | Disjunction '(||)' is associative.
orAssoc ::
    foreach (x :: Bool) ->
    foreach (y :: Bool) ->
    foreach (z :: Bool) ->
    ((x || y) || z) :~: (x || (y || z))
orAssoc False _ _ = Refl
orAssoc True _ _ = Refl

-- | Conjunction '(&&)' is commutative.
andComm :: foreach (x :: Bool) -> foreach (y :: Bool) -> (x && y) :~: (y && x)
andComm False False = Refl
andComm False True = Refl
andComm True False = Refl
andComm True True = Refl

-- | Disjunction '(||)' is commutative.
orComm :: foreach (x :: Bool) -> foreach (y :: Bool) -> (x || y) :~: (y || x)
orComm False False = Refl
orComm False True = Refl
orComm True False = Refl
orComm True True = Refl

-- | De Morgan law for negating a conjunction.
deMorganAnd ::
    foreach (x :: Bool) ->
    foreach (y :: Bool) ->
    not (x && y) :~: (not x || not y)
deMorganAnd False _ = Refl
deMorganAnd True _ = Refl

-- | De Morgan law for negating a disjunction.
deMorganOr ::
    foreach (x :: Bool) ->
    foreach (y :: Bool) ->
    not (x || y) :~: (not x && not y)
deMorganOr False _ = Refl
deMorganOr True _ = Refl
