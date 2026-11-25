# Revision history for dependent-base

## 0.1.0.0 -- 2026-11-25

* Initial release of `dependent-base`:
  * `Prelude.Dependent` and `Data.Function.Dependent` with first-class dependent
    function composition `(.)` and dependent application `($)`.
  * Propositional equality, congruence, substitution, ASCII equational reasoning
    combinators, and the `Inspect` view idiom in `Data.Type.Equality.Dependent`.
  * Constructive decidability (`Dec`, `Reflects`, `ReflectsBool`, `DecEq`) in
    `Data.Decision`.
  * Certified operations and algebraic proof properties for `Bool`, `Maybe`,
    `Either`, `(,)`, `[]`, `Nat`, `Fin`, `Vec`, `All`/`Any`/`Elem`, `Sigma`, and
    `Exists`.
