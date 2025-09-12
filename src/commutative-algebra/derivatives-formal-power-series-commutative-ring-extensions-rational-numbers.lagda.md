# Derivatives of formal power series in commutative ring extensions of the rational numbers

```agda
module commutative-algebra.derivatives-formal-power-series-commutative-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ring-extensions-rational-numbers
open import commutative-algebra.derivatives-formal-power-series-commutative-rings
open import commutative-algebra.formal-power-series-commutative-ring-extensions-rational-numbers

open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "derivative" WDID=Q29175 WD="derivative" disambiguation="of a formal power series in a commutative ring extension of the rational numbers" Agda=derivative-formal-power-series-Rational-Extension-Commutative-Ring}}
of a
[formal power series](commutative-algebra.formal-power-series-commutative-semirings.md)
`Σₙ aₙxⁿ` in a
[commutative ring extension of the rational numbers](commutative-algebra.commutative-ring-extensions-rational-numbers.md)
is its
[derivative](commutative-algebra.derivatives-formal-power-series-commutative-rings.md)
in the corresponding
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  derivative-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R →
    formal-power-series-Rational-Extension-Commutative-Ring R
  derivative-formal-power-series-Rational-Extension-Commutative-Ring =
    derivative-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```
