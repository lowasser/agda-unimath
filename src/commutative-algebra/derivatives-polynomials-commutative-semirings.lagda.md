# Derivatives of polynomials in commutative semirings

```agda
module commutative-algebra.derivatives-polynomials-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.derivatives-formal-power-series-commutative-semirings
open import commutative-algebra.polynomials-commutative-semirings

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import logic.functoriality-existential-quantification
```

</details>

## Idea

The
{{#concept "derivative" WDID=Q29175 WD="derivative" disambiguation="of a polynomial in a commutative semiring" Agda=derivative-polynomial-Commutative-Semiring}}
of a [polynomial](commutative-algebra.polynomials-commutative-semirings.md)
`Σₙ aₙxⁿ` in a
[commutative semiring](commutative-algebra.commutative-semirings.md) is
`Σₙ (n + 1) aₙ₊₁ xⁿ`.

## Definition

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    is-polynomial-derivative-polynomial-Commutative-Semiring :
      (p : polynomial-Commutative-Semiring R) →
      is-polynomial-formal-power-series-Commutative-Semiring
        ( derivative-formal-power-series-Commutative-Semiring
          ( formal-power-series-polynomial-Commutative-Semiring p))
    is-polynomial-derivative-polynomial-Commutative-Semiring (p , is-poly-p) =
      map-tot-exists
        ( λ n n≤k→pₖ=0 k n≤k →
          ap
            ( mul-nat-scalar-Commutative-Semiring R (succ-ℕ k))
            ( n≤k→pₖ=0 (succ-ℕ k) (preserves-leq-succ-ℕ n k n≤k)) ∙
          right-zero-law-mul-nat-scalar-Commutative-Semiring R
            ( succ-ℕ k))
        ( is-poly-p)

  derivative-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R → polynomial-Commutative-Semiring R
  derivative-polynomial-Commutative-Semiring (p , is-poly-p) =
    ( derivative-formal-power-series-Commutative-Semiring p ,
      is-polynomial-derivative-polynomial-Commutative-Semiring (p , is-poly-p))
```
