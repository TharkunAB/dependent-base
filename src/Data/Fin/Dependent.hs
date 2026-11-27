{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ListTuplePuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Bounded natural positions ('Fin') strictly below a Peano bound.
module Data.Fin.Dependent
  ( Fin (..)
  , KnownFin (..)
  , fin
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
import GHC.OverloadedLabels (IsLabel (..))
import GHC.TypeError (ErrorMessage (..), TypeError, Unsatisfiable, unsatisfiable)
import GHC.TypeLits (Symbol, UnconsSymbol)
import GHC.TypeNats.Experimental (FromNatural)
import qualified GHC.TypeNats as TN
import Prelude (Bool (..), Char, Eq (..), Int, Maybe (..), Ord (..), Show, otherwise, (+), (-))

{- Note [Why Fin constructors are named FZ and FS]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Module "Prelude.Dependent" exports both @Nat (Zero, Succ)@ and @Fin (FZ, FS)@
unqualified in one namespace. Distinct constructor prefixes prevent name clashes
across all indexed types in @dependent-base@ ('Zero'/'Succ', 'FZ'/'FS',
'VNil'/'VCons', 'LEZero'/'LESucc', and 'AllNil'/'AllCons').

Do not add @Zero@ and @Succ@ pattern synonyms for 'Fin'. GHC certifies
@-fwrite-source-equations@ tables and refines @foreach@ pattern matrices only on
real data constructors, not on pattern synonyms. Pattern synonyms also lack
promoted type constructors under @-XDataKinds@.

Call sites can write compile-time checked numerals such as @fin 0@ and @fin 1@
(or @#0@ and @#1@ with @-XOverloadedLabels@) instead of nested 'FS'
applications. See Note [Bounded Fin numerals].
-}

-- | A zero-based position strictly below a Peano natural bound.
-- See Note [Why Fin constructors are named FZ and FS].
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

deriving instance Eq (Fin n)
deriving instance Show (Fin n)

{- Note [Bounded Fin numerals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Type 'Fin' omits a 'Prelude.Num' instance by design. Method
'Prelude.fromInteger' receives a runtime 'Prelude.Integer', so @Num (Fin n)@
cannot check @k < n@ at compile time and cannot define total addition,
subtraction, or multiplication on bounded positions.

Class 'KnownFin' steps a type-level natural @k@ against 'Succ' constructors of
the bound @n@ at compile time. Open bounds such as @Fin (Succ (Succ m))@ accept
@0@ and @1@ without knowing @m@. When the remaining bound reaches 'Zero',
'Unsatisfiable' reports a compile-time bounds error that preserves the original
literal and bound type.

Function 'fin' constructs a checked 'Fin' from a visible natural argument, as in
@lookupVec (fin 1) xs@. The 'IsLabel' instance supports @#0@ and @#1@ under
@-XOverloadedLabels@, as in @lookupVec #1 xs@. The 'FromNatural' type instance
provides the matching type-level conversion.
-}

type family IsZeroNat (k :: TN.Nat) :: Bool where
  IsZeroNat 0 = True
  IsZeroNat _ = False

class KnownFinAt (orig :: TN.Nat) (origBound :: Nat) (isZero :: Bool) (k :: TN.Nat) (n :: Nat) where
  finAt :: Fin n

instance
  Unsatisfiable
    ( 'Text "Numeric literal "
        ':<>: 'ShowType orig
        ':<>: 'Text " is out of bounds for "
        ':<>: 'ShowType (Fin origBound)
    ) =>
  KnownFinAt orig origBound isZero k Zero
  where
  finAt = unsatisfiable

instance KnownFinAt orig origBound True k (Succ n) where
  finAt = FZ

instance
  KnownFinAt orig origBound (IsZeroNat (k TN.- 1)) (k TN.- 1) n =>
  KnownFinAt orig origBound False k (Succ n)
  where
  finAt = FS (finAt @orig @origBound @(IsZeroNat (k TN.- 1)) @(k TN.- 1) @n)

-- | Evidence that the type-level natural @k@ is strictly below @n@.
-- See Note [Bounded Fin numerals].
class KnownFin (k :: TN.Nat) (n :: Nat) where
  -- | Construct the runtime 'Fin' value for @k@ below @n@.
  finVal :: Fin n

instance KnownFinAt k n (IsZeroNat k) k n => KnownFin k n where
  finVal = finAt @k @n @(IsZeroNat k) @k @n

-- | Construct a compile-time bounds-checked 'Fin' from a visible natural literal.
-- See Note [Bounded Fin numerals].
fin :: forall (k :: TN.Nat) -> forall {n :: Nat}. KnownFin k n => Fin n
fin (type k) = finVal @k

type ConsFin :: forall {n :: Nat}. Fin n -> Fin (Succ n)
type family ConsFin i where
  ConsFin FZ = FS FZ
  ConsFin (FS i) = FS (FS i)

type FinLit :: TN.Nat -> Nat -> TN.Nat -> forall (n :: Nat) -> Fin n
type family FinLit orig origBound k n where
  FinLit orig origBound _ Zero =
    TypeError
      ( 'Text "Numeric literal "
          ':<>: 'ShowType orig
          ':<>: 'Text " is out of bounds for "
          ':<>: 'ShowType (Fin origBound)
      )
  FinLit _ _ 0 (Succ n) = FZ
  FinLit orig origBound k (Succ n) = ConsFin (FinLit orig origBound (k TN.- 1) n)

type instance FromNatural (Fin n) k = FinLit k n k n

type family DigitVal (orig :: Symbol) (c :: Char) :: TN.Nat where
  DigitVal _ '0' = 0
  DigitVal _ '1' = 1
  DigitVal _ '2' = 2
  DigitVal _ '3' = 3
  DigitVal _ '4' = 4
  DigitVal _ '5' = 5
  DigitVal _ '6' = 6
  DigitVal _ '7' = 7
  DigitVal _ '8' = 8
  DigitVal _ '9' = 9
  DigitVal orig _ =
    TypeError
      ( 'Text "Label #"
          ':<>: 'Text orig
          ':<>: 'Text " is not a non-negative decimal Fin literal."
      )

type family ParseFinDigits (orig :: Symbol) (acc :: TN.Nat) (rest :: Maybe (Char, Symbol)) :: TN.Nat where
  ParseFinDigits _ acc Nothing = acc
  ParseFinDigits orig acc (Just '(c, cs)) =
    ParseFinDigits orig ((acc TN.* 10) TN.+ DigitVal orig c) (UnconsSymbol cs)

type family ParseFinStart (orig :: Symbol) (first :: Maybe (Char, Symbol)) :: TN.Nat where
  ParseFinStart orig Nothing =
    TypeError
      ( 'Text "Label #"
          ':<>: 'Text orig
          ':<>: 'Text " is not a non-negative decimal Fin literal."
      )
  ParseFinStart orig (Just '(c, cs)) =
    ParseFinDigits orig (DigitVal orig c) (UnconsSymbol cs)

type ParseFinLabel (sym :: Symbol) = ParseFinStart sym (UnconsSymbol sym)

instance KnownFin (ParseFinLabel sym) n => IsLabel sym (Fin n) where
  fromLabel = finVal @(ParseFinLabel sym) @n

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
