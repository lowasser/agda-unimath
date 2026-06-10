# Tagged partitions of closed intervals of real numbers

```agda
module real-numbers.tagged-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.partitions-closed-intervals-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import lists.finite-sequences-of-types
open import foundation.function-types
```

</details>

## Idea

## Definition

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  where

  type-tags-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → UU ?
  type-tags-partition-closed-interval-ℝ p =
    Π-fin-sequence
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
      ( type-closed-interval-ℝ l ∘
        fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p)

  tagged-partition-closed-interval-ℝ : UU ?
  tagged-partition-closed-interval-ℝ =
    Σ ( partition-closed-interval-ℝ [a,b])
      ( type-tags-partition-closed-interval-ℝ)
```
