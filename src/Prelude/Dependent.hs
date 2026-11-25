{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Ergonomic Dependent Haskell prelude modeled on @linear-base@ and
-- @agda-prelude@, re-exporting standard @base@ runtime datatypes alongside
-- dependent function composition '(.)', dependent application '($)', indexed
-- containers, dependent pairs, erased existentials, propositional equality, and
-- decidable equality.
module Prelude.Dependent
  ( -- * Core types and classes
    Type
  , Matchability (..)
  , M
  , U
  , Eq (..)
  , Ord (..)
  , Show (..)
  , Num (..)
  , Int
  , Integer
  , Char
  , String
  , Ordering (..)

    -- * Dependent and ordinary function combinators
  , (.)
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

    -- * Booleans, Maybe, Either, and Tuples
  , Bool (..)
  , not
  , (&&)
  , (||)
  , otherwise
  , bool
  , Maybe (..)
  , maybe
  , fromMaybe
  , Either (..)
  , either
  , fst
  , snd
  , swap
  , curry
  , uncurry
  , Iso (..)
  , isoRefl
  , isoSym
  , isoTrans

    -- * Peano naturals, bounded positions, and indexed vectors
  , Nat (..)
  , Size
  , plus
  , type (+)
  , mul
  , minus
  , minNat
  , maxNat
  , natToInt
  , natToInteger
  , LE (..)
  , LTNat
  , Fin (..)
  , finToNat
  , finToInt
  , mkFin
  , weakenFin
  , shiftFin
  , absurdFinZero
  , oppositeFin
  , Vec (..)
  , SomeVec
  , headVec
  , tailVec
  , appendVec
  , mapVec
  , zipVec
  , zipWithVec
  , replicateVec
  , lookupVec
  , tabulateVec
  , toListVec
  , fromListVec
  , fromListExact
  , packListVec

    -- * Lists and indexed list predicates
  , size
  , lengthNat
  , (++)
  , map
  , zip
  , zipWith
  , reverse
  , All (..)
  , Any (..)
  , Elem
  , lookupAll
  , mapAll
  , decAll
  , decAny
  , decElem

    -- * Dependent pairs and existential packages
  , Sigma (..)
  , first
  , second
  , withSigma
  , mapSigma
  , currySigma
  , uncurrySigma
  , pattern Pack
  , type (/\) (..)
  , discardEvidence
  , withEvidence
  , Witness (..)
  , withExists
  , mapExists
  , uncurryExists

    -- * Propositional equality and inspection
  , (:~:) (..)
  , (:~~:) (..)
  , type (~)
  , sym
  , trans
  , cong
  , cong2
  , subst
  , rewrite
  , castWith
  , gcastWith
  , begin
  , stepEq
  , stepRefl
  , (===)
  , qed
  , Inspect (..)
  , inspect

    -- * Constructive decisions
  , Void
  , absurd
  , Not
  , Dec (..)
  , decToBool
  , Reflects (..)
  , ReflectsBool (..)
  , DecEq (..)
  ) where

import Data.Bool.Dependent (Bool (..), bool, not, otherwise, (&&), (||))
import Data.Decision
  ( Dec (..)
  , DecEq (..)
  , Not
  , Reflects (..)
  , ReflectsBool (..)
  , Void
  , absurd
  , decToBool
  )
import Data.Either.Dependent (Either (..), either)
import Data.Exists.Dependent
  ( Witness (..)
  , discardEvidence
  , mapExists
  , pattern Pack
  , uncurryExists
  , withEvidence
  , withExists
  , type (/\) (..)
  )
import Data.Fin.Dependent
  ( Fin (..)
  , absurdFinZero
  , finToInt
  , finToNat
  , mkFin
  , oppositeFin
  , shiftFin
  , weakenFin
  )
import Data.Function.Dependent
  ( applyDep
  , composeDep
  , composeSigma
  , const
  , constDep
  , flip
  , flipDep
  , id
  , idDep
  , on
  , ($)
  , (.)
  )
import Data.Kind (Type)
import Data.List.Dependent (lengthNat, map, reverse, size, zip, zipWith, (++))
import Data.List.Dependent.All
  ( All (..)
  , Any (..)
  , Elem
  , decAll
  , decAny
  , decElem
  , lookupAll
  , mapAll
  )
import Data.Maybe.Dependent (Maybe (..), fromMaybe, maybe)
import Data.Nat.Dependent
  ( LE (..)
  , LTNat
  , Nat (..)
  , Size
  , maxNat
  , minNat
  , minus
  , mul
  , natToInt
  , natToInteger
  , plus
  , type (+)
  )
import Data.Sigma.Dependent
  ( Sigma (..)
  , currySigma
  , first
  , mapSigma
  , second
  , uncurrySigma
  , withSigma
  )
import Data.Tuple.Dependent
  ( Iso (..)
  , curry
  , fst
  , isoRefl
  , isoSym
  , isoTrans
  , snd
  , swap
  , uncurry
  )
import Data.Type.Equality.Dependent
  ( (:~:) (..)
  , (:~~:) (..)
  , Inspect (..)
  , M
  , Matchability (..)
  , U
  , begin
  , castWith
  , cong
  , cong2
  , gcastWith
  , inspect
  , qed
  , rewrite
  , stepEq
  , stepRefl
  , subst
  , sym
  , trans
  , (===)
  , type (~)
  )
import Data.Vec.Dependent
  ( SomeVec
  , Vec (..)
  , appendVec
  , fromListExact
  , fromListVec
  , headVec
  , lookupVec
  , mapVec
  , packListVec
  , replicateVec
  , tabulateVec
  , tailVec
  , toListVec
  , zipVec
  , zipWithVec
  )
import Prelude
  ( Char
  , Eq (..)
  , Int
  , Integer
  , Num (..)
  , Ord (..)
  , Ordering (..)
  , Show (..)
  , String
  )
