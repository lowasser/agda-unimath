# The action on Cauchy approximations of isometries on metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-set-quotients
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The action of [isometries](metric-spaces.isometries-metric-spaces.md) on
[metric spaces](metric-spaces.metric-spaces.md) preserves
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  where

  map-isometry-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space X →
    cauchy-approximation-Metric-Space Y
  map-isometry-cauchy-approximation-Metric-Space =
    map-short-map-cauchy-approximation-Metric-Space
      ( X)
      ( Y)
      ( short-map-isometry-Metric-Space X Y f)
```

## Properties

### Isometries preserve similarity in the Cauchy pseudocompletion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  where abstract

  preserves-sim-isometry-cauchy-pseudocompletion-Metric-Space :
    preserves-sim-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space X)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space Y)
      ( map-isometry-cauchy-approximation-Metric-Space X Y f)
  preserves-sim-isometry-cauchy-pseudocompletion-Metric-Space {x} {y} =
    preserves-sim-short-map-cauchy-pseudocompletion-Metric-Space
      ( X)
      ( Y)
      ( short-map-isometry-Metric-Space X Y f)
      { x}
      { y}
```
