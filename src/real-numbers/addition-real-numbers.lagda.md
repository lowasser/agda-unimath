# Dedekind real numbers

```agda
module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The lower cut (upper cut) of the sum of two real numbers is the set of sums of
elements of their lower (upper) cuts.

```agda
add-subtypes-ℚ : {l : Level} → subtype l ℚ → subtype l ℚ → subtype l ℚ
add-subtypes-ℚ A B q =
  ∃ (ℚ × ℚ) (λ (a , b) → A a ∧ B b ∧ (Id-Prop ℚ-Set (a +ℚ b) q))

module _
  {l : Level} (x y : ℝ l)
  where

  lower-cut-add-ℝ : subtype l ℚ
  lower-cut-add-ℝ = add-subtypes-ℚ (lower-cut-ℝ x) (lower-cut-ℝ y)

  upper-cut-add-ℝ : subtype l ℚ
  upper-cut-add-ℝ = add-subtypes-ℚ (upper-cut-ℝ x) (upper-cut-ℝ y)

  lower-cut-inhabited-add-ℝ : exists ℚ lower-cut-add-ℝ
```
