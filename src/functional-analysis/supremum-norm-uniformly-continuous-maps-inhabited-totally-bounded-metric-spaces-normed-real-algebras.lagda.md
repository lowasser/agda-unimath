# The supremum norm on maps from inhabited totally bounded metric spaces to normed real algebras

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.supremum-norm-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras
open import functional-analysis.supremum-norm-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import linear-algebra.normed-real-algebras

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-nonnegative-real-numbers
open import real-numbers.metric-space-of-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.suprema-families-nonnegative-real-numbers
```

</details>

## Idea

Given a
[uniformly continuous map](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
`f` from an
[inhabited totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
`X` to a [normed real algebra](linear-algebra.normed-real-algebras.md) `V`, the
family of [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md)
`x ↦ ∥f x∥` has a
[supremum](real-numbers.suprema-families-nonnegative-real-numbers.md), generally
denoted $\lVert f \rVert_X$.

We will call this the
{{#concept "supremum norm" Disambiguation="on uniformly continuous maps from inhabited totally bounded metric spaces to normed real algebras"}},
as it is a
[norm on such maps](functional-analysis.normed-real-algebra-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (A : Normed-ℝ-Algebra l4 l5)
  (f :
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
      ( X)
      ( A))
  where

  uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
  uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( f)

  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    type-inhabited-totally-bounded-Metric-Space X → ℝ⁰⁺ l4
  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    map-uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
      ( uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    has-supremum-family-ℝ⁰⁺
      ( l4)
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( f)

  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    ℝ⁰⁺ l4
  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    pr1
      ( has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  real-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    ℝ l4
  real-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    real-ℝ⁰⁺
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-supremum-family-ℝ⁰⁺
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    pr2
      ( has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  is-least-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-ℝ⁰⁺)
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-least-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-least-upper-bound-is-supremum-family-ℝ⁰⁺
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  is-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-upper-bound-family-of-elements-Large-Poset
      ( large-poset-ℝ⁰⁺)
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-upper-bound-is-supremum-family-ℝ⁰⁺
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
      ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
```
