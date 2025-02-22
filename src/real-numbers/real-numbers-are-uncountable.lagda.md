# The real numbers are uncountable

```agda
module real-numbers.real-numbers-are-uncountable where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.surjective-maps
open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import set-theory.uncountable-sets
open import elementary-number-theory.positive-rational-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.minimum-real-numbers
open import foundation.dependent-pair-types
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

```agda
differing-sequence :
  (a : ℕ → ℝ lzero) →
  is-surjective a →
  Σ
    ( ℕ → ℝ lzero)
    ( λ x →
      Σ
        ( ℕ → ℝ lzero)
        ( λ y → {!   !})
```
