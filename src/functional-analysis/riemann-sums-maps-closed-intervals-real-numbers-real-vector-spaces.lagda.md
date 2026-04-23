# Riemann sums of maps from closed intervals in ℝ to real vector spaces

```agda
module functional-analysis.riemann-sums-maps-closed-intervals-real-numbers-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-real-vector-spaces

open import lists.finite-sequences

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-poset-closed-intervals-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers
```

</details>

## Idea

Given a function `f` mapping a
[closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]` of the
[real numbers](real-numbers.dedekind-real-numbers.md) into a
[real vector space](linear-algebra.real-vector-spaces.md) `V`, the area of the
Riemann rectangle of `f` on `[a, b]` is `(b - a) * f a`. Given a
[partition](real-numbers.partitions-closed-intervals-real-numbers.md) of
`[a, b]`, the
{{#concept "Riemann sum" WDID=Q1156903 WD="Riemann sum" Disambiguation="of a map from a closed interval of ℝ into a real vector space, over a partition of that interval" Agda=riemann-sum-partition-closed-interval-ℝ}}
of `f` on that partition is the sum of the areas of the Riemann rectangles over
the closed intervals in that partition.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-ℝ-Vector-Space V)
  where

  area-riemann-rectangle-closed-interval-ℝ-Vector-Space :
    ([c,d] : closed-interval-ℝ l1 l1) →
    leq-closed-interval-ℝ [c,d] [a,b] →
    type-ℝ-Vector-Space V
  area-riemann-rectangle-closed-interval-ℝ-Vector-Space
    ((c , d) , c≤d) (a≤c , d≤b) =
    mul-ℝ-Vector-Space
      ( V)
      ( d -ℝ c)
      ( f (c , a≤c , transitive-leq-ℝ c d b d≤b c≤d))

  fin-sequence-area-riemann-rectangle-closed-interval-ℝ-Vector-Space :
    (p : partition-closed-interval-ℝ [a,b]) →
    fin-sequence
      ( type-ℝ-Vector-Space V)
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
  fin-sequence-area-riemann-rectangle-closed-interval-ℝ-Vector-Space p i =
    area-riemann-rectangle-closed-interval-ℝ-Vector-Space
      ( fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p i)
      ( leq-fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p i)

  riemann-sum-partition-closed-interval-ℝ-Vector-Space :
    (p : partition-closed-interval-ℝ [a,b]) →
    type-ℝ-Vector-Space V
  riemann-sum-partition-closed-interval-ℝ-Vector-Space p =
    sum-fin-sequence-type-ℝ-Vector-Space
      ( V)
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
      ( fin-sequence-area-riemann-rectangle-closed-interval-ℝ-Vector-Space p)
```
