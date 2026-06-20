# Uniformly continuous maps from inhabited, totally bounded metric spaces to normed real algebras

```agda
module functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels

open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import linear-algebra.normed-real-algebras

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from an
[inhabited totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
to a [normed real vector space](linear-algebra.normed-real-vector-spaces.md)
themselves form a [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (A : Normed-ℝ-Algebra l4 l5)
  (let V = normed-vector-space-Normed-ℝ-Algebra A)
  where

  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    Metric-Space (l1 ⊔ l2 ⊔ l4 ⊔ l5) (l1 ⊔ l4)
  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)

  set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    Set (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    set-Metric-Space
      ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    UU (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    type-Set
      ( set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
```
