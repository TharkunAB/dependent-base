{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ListTuplePuns #-}

-- | Constructive decidability ('Dec'), Boolean reflection ('Reflects'),
-- propositional negation ('Not'), and certified decidable equality ('DecEq').
module Data.Decision
  ( Void
  , absurd
  , Not
  , Dec (..)
  , decToBool
  , Reflects (..)
  , ReflectsBool (..)
  , decToReflectsBool
  , reflectsBoolToDec
  , decNot
  , decAnd
  , decOr
  , decImp
  , DecEq (..)
  ) where

import Data.Fin.Dependent (Fin (..))
import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..))
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, cong2)
import Data.Vec.Dependent (Vec (..))
import Data.Void (Void, absurd)
import Prelude (Bool (..), Either (..), Maybe (..), Ordering (..))

-- | Constructive refutation of proposition @p@.
type Not (p :: Type) = p -> Void

-- | Constructive decision of proposition @p@: either a witness ('Yes') or a
-- refutation ('No').
data Dec (p :: Type)
  = Yes p
  | No (Not p)

-- | Erase the proof or refutation in a 'Dec' value to a 'Bool'.
decToBool :: forall p. Dec p -> Bool
decToBool (Yes _) = True
decToBool (No _)  = False

-- | Relate proposition @p@ to a specific Boolean truth value.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: forall {p}. p -> Reflects p True
  OfFalse :: forall {p}. Not p -> Reflects p False

-- | Existentially pair a Boolean truth outcome with its 'Reflects' evidence.
data ReflectsBool (p :: Type) where
  ReflectTrue  :: forall {p}. p -> ReflectsBool p
  ReflectFalse :: forall {p}. Not p -> ReflectsBool p

-- | Convert a 'Dec' decision to 'ReflectsBool'.
decToReflectsBool :: forall p. Dec p -> ReflectsBool p
decToReflectsBool (Yes ev)   = ReflectTrue ev
decToReflectsBool (No notEv) = ReflectFalse notEv

-- | Convert 'ReflectsBool' evidence back into 'Dec'.
reflectsBoolToDec :: forall p. ReflectsBool p -> Dec p
reflectsBoolToDec (ReflectTrue ev)     = Yes ev
reflectsBoolToDec (ReflectFalse notEv) = No notEv

-- | Decide the negation of a decidable proposition.
decNot :: forall p. Dec p -> Dec (Not p)
decNot (Yes p)   = No (\notP -> notP p)
decNot (No notP) = Yes notP

-- | Decide the conjunction (product) of two decidable propositions.
decAnd :: forall p q. Dec p -> Dec q -> Dec (p, q)
decAnd (No notP) _         = No (\(p, _) -> notP p)
decAnd (Yes _)   (No notQ) = No (\(_, q) -> notQ q)
decAnd (Yes p)   (Yes q)   = Yes (p, q)

-- | Decide the disjunction ('Either') of two decidable propositions.
decOr :: forall p q. Dec p -> Dec q -> Dec (Either p q)
decOr (Yes p)   _         = Yes (Left p)
decOr (No _)    (Yes q)   = Yes (Right q)
decOr (No notP) (No notQ) = No (\case
  Left p  -> notP p
  Right q -> notQ q)

-- | Decide the implication @p -> q@ between two decidable propositions.
decImp :: forall p q. Dec p -> Dec q -> Dec (p -> q)
decImp (No notP) _         = Yes (\p -> absurd (notP p))
decImp (Yes _)   (Yes q)   = Yes (\_ -> q)
decImp (Yes p)   (No notQ) = No (\f -> notQ (f p))

-- | Types with decidable propositional equality on runtime values.
class DecEq a where
  -- | Decide whether @x@ and @y@ are propositionally equal.
  decEq :: foreach (x :: a) -> foreach (y :: a) -> Dec (x :~: y)

instance DecEq () where
  decEq () () = Yes Refl

instance DecEq Bool where
  decEq False False = Yes Refl
  decEq False True  = No (\case {})
  decEq True  False = No (\case {})
  decEq True  True  = Yes Refl

instance DecEq Ordering where
  decEq LT LT = Yes Refl
  decEq LT EQ = No (\case {})
  decEq LT GT = No (\case {})
  decEq EQ LT = No (\case {})
  decEq EQ EQ = Yes Refl
  decEq EQ GT = No (\case {})
  decEq GT LT = No (\case {})
  decEq GT EQ = No (\case {})
  decEq GT GT = Yes Refl

instance DecEq Nat where
  decEq Zero     Zero     = Yes Refl
  decEq Zero     (Succ _) = No (\case {})
  decEq (Succ _) Zero     = No (\case {})
  decEq (Succ m) (Succ n) = case decEq m n of
    Yes eq  -> Yes (cong Succ eq)
    No notE -> No (\case Refl -> notE Refl)

instance DecEq (Fin n) where
  decEq FZ     FZ     = Yes Refl
  decEq FZ     (FS _) = No (\case {})
  decEq (FS _) FZ     = No (\case {})
  decEq (FS i) (FS j) = case decEq i j of
    Yes eq  -> Yes (cong FS eq)
    No notE -> No (\case Refl -> notE Refl)

instance DecEq a => DecEq (Maybe a) where
  decEq Nothing  Nothing  = Yes Refl
  decEq Nothing  (Just _) = No (\case {})
  decEq (Just _) Nothing  = No (\case {})
  decEq (Just x) (Just y) = case decEq x y of
    Yes eq  -> Yes (cong Just eq)
    No notE -> No (\case Refl -> notE Refl)

instance (DecEq a, DecEq b) => DecEq (Either a b) where
  decEq (Left x)  (Left y)  = case decEq x y of
    Yes eq  -> Yes (cong Left eq)
    No notE -> No (\case Refl -> notE Refl)
  decEq (Left _)  (Right _) = No (\case {})
  decEq (Right _) (Left _)  = No (\case {})
  decEq (Right x) (Right y) = case decEq x y of
    Yes eq  -> Yes (cong Right eq)
    No notE -> No (\case Refl -> notE Refl)

instance (DecEq a, DecEq b) => DecEq (a, b) where
  decEq (x1, y1) (x2, y2) = case decEq x1 x2 of
    No notX -> No (\case Refl -> notX Refl)
    Yes eqX -> case decEq y1 y2 of
      No notY -> No (\case Refl -> notY Refl)
      Yes eqY -> Yes (cong2 (,) eqX eqY)

instance DecEq a => DecEq [a] where
  decEq []       []       = Yes Refl
  decEq []       (_ : _)  = No (\case {})
  decEq (_ : _)  []       = No (\case {})
  decEq (x : xs) (y : ys) = case decEq x y of
    No notH -> No (\case Refl -> notH Refl)
    Yes eqH -> case decEq xs ys of
      No notT -> No (\case Refl -> notT Refl)
      Yes eqT -> Yes (cong2 (:) eqH eqT)

instance DecEq a => DecEq (Vec a n) where
  decEq VNil         VNil         = Yes Refl
  decEq (VCons x xs) (VCons y ys) = case decEq x y of
    No notH  -> No (\case Refl -> notH Refl)
    Yes Refl -> case decEq xs ys of
      No notT  -> No (\case Refl -> notT Refl)
      Yes Refl -> Yes Refl
