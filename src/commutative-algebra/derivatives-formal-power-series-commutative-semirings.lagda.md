# Derivatives of formal power series in commutative semirings

```agda
module commutative-algebra.derivatives-formal-power-series-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "derivative" WDID=Q29175 WD="derivative" disambiguation="of a formal power series in a commutative semiring" Agda=derivative-formal-power-series-Commutative-Semiring}}
of a
[formal power series](commutative-algebra.formal-power-series-commutative-semirings.md)
`Σₙ aₙxⁿ` in a
[commutative semiring](commutative-algebra.commutative-semirings.md) is
`Σₙ (n + 1) aₙ₊₁ xⁿ`.

## Definition

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  derivative-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R →
    formal-power-series-Commutative-Semiring R
  derivative-formal-power-series-Commutative-Semiring x =
    formal-power-series-coefficients-Commutative-Semiring
      ( λ n →
        mul-nat-scalar-Commutative-Semiring R
          ( succ-ℕ n)
          ( coefficient-formal-power-series-Commutative-Semiring x (succ-ℕ n)))
```
