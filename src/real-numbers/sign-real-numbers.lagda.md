# Signs of real numbers

```agda
module real-numbers.sign-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
```

</details>

## Possible signs

We define what it means for a real number to be zero, positive, or negative, and
show that those options are mutually exclusive.

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

  not-is-positive-and-negative : ¬ (is-positive-ℝ × is-negative-ℝ)
  not-is-positive-and-negative = is-disjoint-cut-ℝ x zero-ℚ

  not-is-zero-and-negative : ¬ (is-zero-ℝ × is-negative-ℝ)
  not-is-zero-and-negative (is-zero , is-neg) =
    is-nonzero-is-positive-ℚ (backward-implication (is-zero zero-ℚ) is-neg) refl

  not-is-zero-and-positive : ¬ (is-zero-ℝ × is-positive-ℝ)
  not-is-zero-and-positive (is-zero , is-pos) =
    elim-exists
      empty-Prop
      (λ q (0<q , in-lower-q) →
          is-disjoint-cut-ℝ x q (in-lower-q , forward-implication (is-zero q) (is-positive-le-zero-ℚ q 0<q)))
      (forward-implication (is-rounded-lower-cut-ℝ x zero-ℚ) is-pos)
```

### The sign of a real number

```agda
sign-ℝ : {l : Level} → ℝ l → UU l
sign-ℝ x = is-negative-ℝ x + (is-zero-ℝ x + is-positive-ℝ x)

signed-ℝ : (l : Level) → UU (lsuc l)
signed-ℝ l = Σ (ℝ l) sign-ℝ
```

### The negation of a positive real is negative, and vice versa

```
neg-positive-is-negative-ℝ :
  {l : Level} → (x : ℝ l) → is-positive-ℝ x → is-negative-ℝ (neg-ℝ x)
neg-positive-is-negative-ℝ x H = H

neg-negative-is-positive-ℝ :
  {l : Level} → (x : ℝ l) → is-negative-ℝ x → is-positive-ℝ (neg-ℝ x)
neg-negative-is-positive-ℝ x H = H
```
