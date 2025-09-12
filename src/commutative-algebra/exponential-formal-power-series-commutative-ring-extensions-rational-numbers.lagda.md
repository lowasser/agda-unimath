# The exponential formal power series in commutative ring extensions of the rational numbers

```agda
module commutative-algebra.exponential-formal-power-series-commutative-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ring-extensions-rational-numbers
open import commutative-algebra.formal-power-series-commutative-ring-extensions-rational-numbers

open import elementary-number-theory.factorials
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

In any
[commutative ring extension of the rational numbers](commutative-algebra.commutative-ring-extensions-rational-numbers.md),
the
{{#concept "exponential formal power series" disambiguation="in a commutative ring extension of the rational numbers" Agda=exp-formal-power-series-Rational-Extension-Commutative-Ring}}
is the unique
[formal power series](commutative-algebra.formal-power-series-commutative-ring-extensions-rational-numbers.md)
with constant term 1 whose
[derivative](commutative-algebra.derivatives-formal-power-series-commutative-rings.md)
is itself.

## Definition

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  exp-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R
  exp-formal-power-series-Rational-Extension-Commutative-Ring =
    formal-power-series-coefficients-Rational-Extension-Commutative-Ring R
      ( λ n →
        map-initial-hom-Rational-Extension-Commutative-Ring R
          ( reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n)))
```
