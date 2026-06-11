# Riemann integrable maps from closed intervals of real numbers to normed real vector spaces

```agda
module functional-analysis.riemann-integrable-maps-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.riemann-sums-tagged-partitions-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.limits-of-sequences-metric-spaces

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.standard-uniform-partitions-closed-intervals-real-numbers
open import real-numbers.tagged-partitions-closed-intervals-real-numbers
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
  where

  is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → subtype (lsuc l1) (ℚ⁺ → ℚ⁺)
  is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space
    x μ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( tagged-partition-closed-interval-ℝ [a,b])
          ( λ tp →
            hom-Prop
              ( leq-prop-ℝ⁰⁺
                ( mesh-tagged-partition-closed-interval-ℝ [a,b] tp)
                ( nonnegative-real-ℚ⁺ (μ ε)))
              ( neighborhood-prop-Normed-ℝ-Vector-Space
                ( V)
                ( ε)
                ( riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
                  ( V)
                  ( [a,b])
                  ( f)
                  ( tp))
                ( x))))

  is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space :
    subtype (lsuc l1) (type-Normed-ℝ-Vector-Space V)
  is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space x =
    ∃ ( ℚ⁺ → ℚ⁺)
      ( is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space
        ( x))

  is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → UU (lsuc l1)
  is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space)

  is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1 ⊔ l2)
  is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space =
    Σ ( type-Normed-ℝ-Vector-Space V)
      ( is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space)
```

## Properties

### If a function is Riemann integrable, the integral is the limit as `n → ∞` of the Riemann sum on the standard uniform partition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  ((S , is-integral-S) :
    is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f))
  where abstract

  is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space :
    is-limit-sequence-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ
        ( V)
        ( [a,b])
        ( f))
      ( S)
  is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space =
    elim-exists
      ( is-limit-prop-sequence-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ
          ( V)
          ( [a,b])
          ( f))
        ( S))
      ( λ μ is-mod-μ →
        intro-exists
          ( λ ε → pred-nonzero-ℕ (pr1 (smaller-reciprocal-ℚ⁺ (μ ε))))
          ( λ ε n N≤n →
            is-mod-μ
              ( ε)
              ( tag-lower-bounds-partition-closed-interval-ℝ
                ( [a,b])
                ( partition-standard-uniform-partition-closed-interval-ℝ
                  ( [a,b])
                  ( n)))
              {!   !}))
      ( is-integral-S)
```
