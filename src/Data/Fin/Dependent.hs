{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Bounded natural positions ('Fin') strictly below a Peano bound.
module Data.Fin.Dependent
  ( Fin (..)
  , finToNat
  , finToInt
  , mkFin
  , weakenFin
  , shiftFin
  , absurdFinZero
  , lastFin
  , oppositeFin
  ) where

import Data.Nat.Dependent (Nat (..), plus)
import Prelude (Eq (..), Int, Maybe (..), Ord (..), Show, otherwise, (+), (-))

-- | A zero-based position strictly below a Peano natural bound.
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

deriving instance Eq (Fin n)
deriving instance Show (Fin n)

-- | Forget the upper bound and return the underlying Peano natural.
finToNat :: forall (n :: Nat). Fin n -> Nat
finToNat FZ     = Zero
finToNat (FS i) = Succ (finToNat i)

-- | Convert a bounded position to a non-negative machine 'Int'.
finToInt :: forall (n :: Nat). Fin n -> Int
finToInt FZ     = 0
finToInt (FS i) = 1 + finToInt i

-- | Convert a non-negative 'Int' into a position strictly below @n@.
mkFin :: foreach (n :: Nat) -> Int -> Maybe (Fin n)
mkFin n position
  | position < 0 = Nothing
  | otherwise    = go n position
  where
    go :: foreach (m :: Nat) -> Int -> Maybe (Fin m)
    go Zero     _ = Nothing
    go (Succ m) k =
      if k == 0
        then Just FZ
        else case go m (k - 1) of
          Nothing      -> Nothing
          Just smaller -> Just (FS smaller)

-- | Embed @Fin n@ into @Fin (Succ n)@ without changing its numeric value.
weakenFin :: forall (n :: Nat). Fin n -> Fin (Succ n)
weakenFin FZ     = FZ
weakenFin (FS i) = FS (weakenFin i)

-- | Shift a position in @Fin n@ upward by @m@ steps into @Fin (plus m n)@.
shiftFin :: forall (n :: Nat). foreach (m :: Nat) -> Fin n -> Fin (plus m n)
shiftFin Zero     i = i
shiftFin (Succ m) i = FS (shiftFin m i)

-- | Refute an impossible position in @Fin Zero@.
absurdFinZero :: forall a. Fin Zero -> a
absurdFinZero = \case {}

-- | Maximal position @n@ inside @Fin (Succ n)@.
lastFin :: foreach (n :: Nat) -> Fin (Succ n)
lastFin Zero     = FZ
lastFin (Succ n) = FS (lastFin n)

-- | Mirror a position @i@ inside @Fin n@ to @n - 1 - i@.
oppositeFin :: foreach (n :: Nat) -> Fin n -> Fin n
oppositeFin Zero     = \case {}
oppositeFin (Succ n) = \case
  FZ   -> lastFin n
  FS i -> weakenFin (oppositeFin n i)
