# The vector space of uniformly continuous functions into normed real vector spaces

```agda
module linear-algebra.vector-space-of-uniformly-continuous-functions-into-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.function-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.subsets-real-vector-spaces
open import linear-algebra.subspaces-real-vector-spaces

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

Given a [metric space](metric-spaces.metric-spaces.md) `X` and a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, the
[uniformly continuous functions](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from `X` to `V` form a
[real vector space](linear-algebra.real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (NV : Normed-ℝ-Vector-Space l3 l4)
  (let V = vector-space-Normed-ℝ-Vector-Space NV)
  (let MV = metric-space-Normed-ℝ-Vector-Space NV)
  where

  abstract
    contains-zero-uniformly-continuous-map-Normed-ℝ-Vector-Space :
      contains-zero-subset-ℝ-Vector-Space
        ( function-ℝ-Vector-Space (type-Metric-Space X) V)
        ( is-uniformly-continuous-prop-map-Metric-Space X MV)
    contains-zero-uniformly-continuous-map-Normed-ℝ-Vector-Space =
      is-uniformly-continuous-map-const-map-Metric-Space
        ( X)
        ( MV)
        ( zero-ℝ-Vector-Space V)

    is-closed-under-addition-uniformly-continuous-map-Normed-ℝ-Vector-Space :
      is-closed-under-addition-subset-ℝ-Vector-Space
        ( function-ℝ-Vector-Space (type-Metric-Space X) V)
        ( is-uniformly-continuous-prop-map-Metric-Space X MV)
    is-closed-under-addition-uniformly-continuous-map-Normed-ℝ-Vector-Space
      f g uc-f uc-g =
      is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
        ( X)
        ( MV)
        ( comp-uniformly-continuous-map-Metric-Space
          ( X)
          ( product-Metric-Space MV MV)
          ( MV)
          ( uniformly-continuous-map-add-pair-Normed-ℝ-Vector-Space NV)
          ( diagonal-product-uniformly-continuous-map-Metric-Space
            ( X)
            ( MV)
            ( MV)
            ( f , uc-f)
            ( g , uc-g)))

    is-closed-under-scalar-multiplication-uniformly-continuous-map-Normed-ℝ-Vector-Space :
      is-closed-under-scalar-multiplication-subset-ℝ-Vector-Space
        ( function-ℝ-Vector-Space (type-Metric-Space X) V)
        ( is-uniformly-continuous-prop-map-Metric-Space X MV)
    is-closed-under-scalar-multiplication-uniformly-continuous-map-Normed-ℝ-Vector-Space
      c f uc-f =
      is-uniformly-continuous-map-comp-Metric-Space
        ( X)
        ( MV)
        ( MV)
        ( mul-Normed-ℝ-Vector-Space NV c)
        ( f)
        ( is-uniformly-continuous-map-mul-Normed-ℝ-Vector-Space NV c)
        ( uc-f)

  subspace-uniformly-continuous-map-Normed-ℝ-Vector-Space :
    subspace-ℝ-Vector-Space
      ( l1 ⊔ l2 ⊔ l3)
      ( function-ℝ-Vector-Space (type-Metric-Space X) V)
  subspace-uniformly-continuous-map-Normed-ℝ-Vector-Space =
    ( is-uniformly-continuous-prop-map-Metric-Space X MV ,
      contains-zero-uniformly-continuous-map-Normed-ℝ-Vector-Space ,
      is-closed-under-addition-uniformly-continuous-map-Normed-ℝ-Vector-Space ,
      is-closed-under-scalar-multiplication-uniformly-continuous-map-Normed-ℝ-Vector-Space)

  vector-space-uniformly-continuous-map-Normed-ℝ-Vector-Space :
    ℝ-Vector-Space l3 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  vector-space-uniformly-continuous-map-Normed-ℝ-Vector-Space =
    vector-space-subspace-ℝ-Vector-Space
      ( function-ℝ-Vector-Space (type-Metric-Space X) V)
      ( subspace-uniformly-continuous-map-Normed-ℝ-Vector-Space)
```
