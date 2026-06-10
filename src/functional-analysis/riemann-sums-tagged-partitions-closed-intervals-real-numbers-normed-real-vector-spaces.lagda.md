# Riemann sums over tagged partitions of a closed interval in the real numbers of functions from that interval to real vector spaces

```agda
module functional-analysis.riemann-sums-tagged-partitions-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.sums-of-finite-sequences-of-elements-normed-real-vector-spaces
open import real-numbers.tagged-partitions-closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import lists.finite-sequences
open import foundation.function-types
open import foundation.universe-levels
open import linear-algebra.normed-real-vector-spaces
open import real-numbers.partitions-closed-intervals-real-numbers
open import foundation.dependent-pair-types
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  (tp@(p , t) : tagged-partition-closed-interval-ℝ [a,b])
  (let n = pred-length-partition-closed-interval-ℝ [a,b] p)
  where

  fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    fin-sequence (type-Normed-ℝ-Vector-Space V) n
  fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    f ∘ fin-sequence-tags-elements-tagged-partition-closed-interval-ℝ [a,b] tp

  fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    fin-sequence (ℝ l1) n
  fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    width-closed-interval-ℝ ∘
    fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p

  riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V
  riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    sum-fin-sequence-type-Normed-ℝ-Vector-Space
      ( V)
      ( n)
      ( λ i →
        mul-Normed-ℝ-Vector-Space V
          ( fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
            ( i))
          ( fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
            ( i)))
```
