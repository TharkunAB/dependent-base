# dependent-base

`dependent-base` is a standard library for Dependent Haskell. It follows the module organization of [`linear-base`](https://github.com/tweag/linear-base): modules re-export GHC `base` runtime datatypes directly (`Bool`, `Maybe`, `Either`, `(,)`, `[]`, `Ordering`, `Void`, `(:~:)`, `(:~~:)`, `Sigma`, `Exists`) without wrapper types or data copying, and pair them with certified total operations, indexed containers, decision procedures, and proof combinators.

All modules use `{-# LANGUAGE DependentTypes #-}` and ASCII GHC `base` identifiers. Ordinary Haskell modules (including `Haskell2010` modules without `-XDependentTypes`) can import `dependent-base` interfaces directly.

## Quick example

```haskell
{-# LANGUAGE DependentTypes #-}

module Example where

import Data.Nat.Dependent.Properties (plusZero)
import Prelude.Dependent

zeros :: foreach (n :: Nat) -> Vec Nat n
zeros Zero     = VNil
zeros (Succ n) = VCons Zero (zeros n)

-- Dependent (.) composes indexed producers and compound equality proofs
-- with constructors, lambdas, overloaded numerals, and certified functions.
zerosPlusOne :: foreach (n :: Nat) -> Vec Nat (plus 1 n)
zerosPlusOne = zeros . plus 1

plusZeroSucc :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusZeroSucc = plusZero . Succ
```

## Module hierarchy

| Module | Contents |
| --- | --- |
| `Prelude.Dependent` | Dependent prelude re-exporting `(.)`, `($)`, `base` types, `Nat`, `Fin`, `Vec`, `All`, `Sigma`, `Pack`, `(:~:)`, `Inspect`, and `DecEq` |
| `Data.Function.Dependent` | Dependent `(.)`, `composeDep`, `composeSigma`, `($)`, `applyDep`, `idDep`, `constDep`, `flipDep`, `on` |
| `Data.Type.Equality.Dependent` | `(:~:)`, `(:~~:)`, `cong`, `cong2`, `congApp`, `subst`, `rewrite`, `begin`, `stepEq`, `stepRefl`, `(===)`, `qed`, `Inspect`, `inspect` |
| `Data.Decision` | `Void`, `absurd`, `Not`, `Dec`, `Reflects`, `ReflectsBool`, `DecEq` |
| `Data.Bool.Dependent` | Certified `Bool` operations and Boolean algebra laws |
| `Data.Maybe.Dependent` | Certified `Maybe` operations, `mapMaybe`, `catMaybes`, and functor/round-trip laws |
| `Data.Either.Dependent` | Certified `Either` operations and sum isomorphism laws |
| `Data.Tuple.Dependent` | Certified pair projections, `swap`, `Iso`, and product/distributivity isomorphisms |
| `Data.Nat.Dependent` | Peano `Nat` with `Num`/`FromNatural` literals, `plus`, `mul`, `minus`, `minNat`, `maxNat`, `eqNat`, `LE`, `LTNat` |
| `Data.Nat.Dependent.Properties` | Semiring laws (`plusZero`, `plusSucc`, `plusAssoc`, `plusComm`, `mulDistribL`, `mulDistribR`, `mulAssoc`, `mulComm`) and `decLE` |
| `Data.Fin.Dependent` | Bounded `Fin` indices, `mkFin`, `weakenFin`, `shiftFin`, `oppositeFin`, `absurdFinZero` |
| `Data.Vec.Dependent` | Length-indexed `Vec`, `SomeVec`, list boundary adapters, `lookupVec`, `tabulateVec`, `reverseVec` |
| `Data.Vec.Dependent.Properties` | `SplitVec`, `vconsCong`, `appendVecNilL`, `appendVecCons`, `appendVecNilR`, `appendVecAssoc`, `splitAtAppendVec` |
| `Data.List.Dependent` | Certified `size`, `append`, `shunt`, `reverseShunt`, `takeSize`, and `base` list operations |
| `Data.List.Dependent.Properties` | Length, append, map, zip, and `reverseShuntInvolutive` laws |
| `Data.List.Dependent.All` | Universal (`All`) and existential (`Any`) list predicates, `Elem`, `lookupAll`, `decAll`, `decAny`, `decElem` |
| `Data.Sigma.Dependent` | Retained dependent pairs (`Sigma`, `first`, `second`, `withSigma`, `mapSigma`, `currySigma`, `uncurrySigma`) |
| `Data.Exists.Dependent` | Erased existential packages (`Pack`, `(/\)`, `Witness`, `withExists`, `mapExists`, `uncurryExists`) |

## Building and testing

Build and run the test suite with a Dependent Haskell GHC compiler:

```bash
cabal build --with-compiler=/path/to/ghc all
cabal test --with-compiler=/path/to/ghc all
```

## License

BSD-3-Clause. See [LICENSE](LICENSE).
