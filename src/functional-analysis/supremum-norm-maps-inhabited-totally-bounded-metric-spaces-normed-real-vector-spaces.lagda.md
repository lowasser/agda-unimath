# The supremum norm on maps from inhabited totally bounded metric spaces to normed real vector spaces

```agda
module functional-analysis.supremum-norm-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import real-numbers.inhabited-totally-bounded-subsets-nonnegative-real-numbers
open import analysis.metric-abelian-groups
open import foundation.identity-types
open import elementary-number-theory.positive-rational-numbers
open import order-theory.least-upper-bounds-large-posets
open import linear-algebra.function-real-vector-spaces
open import metric-spaces.metrics
open import foundation.action-on-identifications-functions
open import foundation.universe-levels
open import real-numbers.nonnegative-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import analysis.metric-abelian-groups-of-uniformly-continuous-maps-into-metric-abelian-groups
open import foundation.logical-equivalences
open import foundation.dependent-pair-types
open import metric-spaces.metrics-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
open import real-numbers.suprema-families-nonnegative-real-numbers
open import real-numbers.suprema-families-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.metric-space-of-nonnegative-real-numbers
open import linear-algebra.normed-real-vector-spaces
open import functional-analysis.metric-abelian-groups-normed-real-vector-spaces
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (f :
    uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Vector-Space V))
  where

  uniformly-continuous-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
  uniformly-continuous-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    comp-uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-ℝ⁰⁺ l4)
      ( uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space V)
      ( f)

  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    type-inhabited-totally-bounded-Metric-Space X → ℝ⁰⁺ l4
  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    map-uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
      ( uniformly-continuous-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  abstract
    has-supremum-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
      has-supremum-family-ℝ⁰⁺
        ( l4)
        ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
    has-supremum-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
      has-supremum-has-supremum-im-ℝ⁰⁺
        ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
        ( has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺
          ( im-uniformly-continuous-map-inhabited-totally-bounded-Metric-Space
            ( X)
            ( metric-space-ℝ⁰⁺ l4)
            ( uniformly-continuous-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)))

  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    ℝ⁰⁺ l4
  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    pr1
      ( has-supremum-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-supremum-family-ℝ⁰⁺
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    pr2
      ( has-supremum-map-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```

## Properties

### The supremum norm is a metric on the metric space of uniformly continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where

  type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    UU (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Vector-Space V)

  metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Metric-Ab (l1 ⊔ l2 ⊔ l4 ⊔ l5) (l1 ⊔ l4)
  metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    metric-ab-uniformly-continuous-map-Metric-Ab
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-ab-Normed-ℝ-Vector-Space V)

  zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
  zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    zero-Metric-Ab
      ( metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l4 ⊔ l5) (l1 ⊔ l4)
  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    metric-space-Metric-Ab
      ( metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space →
    type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space →
    ℝ⁰⁺ l4
  dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f g =
    sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( diff-Metric-Ab
        ( metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
        ( f)
        ( g))

  abstract
    right-zero-law-dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
      (f : type-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space) →
      dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( f)
        ( zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space) ＝
      sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( f)
    right-zero-law-dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      f =
      ap
        ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V))
        ( right-zero-law-diff-Metric-Ab
          ( metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
          ( f))

    is-metric-dist-sup-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
      is-metric-of-Metric-Space
        ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
        ( dist-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
    is-metric-dist-sup-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        d f@(map-f , uc-f) g@(map-g , uc-g)
      =
      is-least-upper-bound-is-supremum-family-ℝ
        ( λ x → dist-Normed-ℝ-Vector-Space V (map-f x) (map-g x))
        ( _)
        ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V)
          ( _))
      ( real-ℚ⁺ d)

    is-triangular-


```
