# Signs of real numbers

```agda
module real-numbers.sign-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

```agda
module _
  {l : Level} (x : ℝ l)
  where

  is-positive-ℝ : UU l
  is-positive-ℝ = is-in-lower-cut-ℝ x zero-ℚ

  is-zero-ℝ : UU l
  is-zero-ℝ = has-same-elements-subtype is-positive-prop-ℚ (upper-cut-ℝ x)

  is-negative-ℝ : UU l
  is-negative-ℝ = is-in-upper-cut-ℝ x zero-ℚ

  sign-ℝ : UU l
  sign-ℝ = is-negative-ℝ + (is-zero-ℝ + is-positive-ℝ)

  not-is-positive-and-negative : ¬ (is-positive-ℝ × is-negative-ℝ)
  not-is-positive-and-negative = is-disjoint-cut-ℝ x zero-ℚ

  not-is-zero-and-negative : ¬ (is-zero-ℝ × is-negative-ℝ)
  not-is-zero-and-negative (is-zero , is-neg) =
    is-nonzero-is-positive-ℚ (backward-implication (is-zero zero-ℚ) is-neg) refl

  not-is-zero-and-positive : ¬ (is-zero-ℝ × is-positive-ℝ)
  not-is-zero-and-positive (is-zero , is-pos) =
    (elim-exists
      empty-Prop
      (λ q (0<q , in-lower-q) →
          is-disjoint-cut-ℝ x q (in-lower-q , forward-implication (is-zero q) (is-positive-le-zero-ℚ q 0<q)))
      (forward-implication (is-rounded-lower-cut-ℝ x zero-ℚ) is-pos))

signed-ℝ : (l : Level) → UU (lsuc l)
signed-ℝ l = Σ (ℝ l) sign-ℝ
```
