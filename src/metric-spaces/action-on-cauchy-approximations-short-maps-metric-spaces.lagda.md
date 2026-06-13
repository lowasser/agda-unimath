# The action on Cauchy approximations of short maps in metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-set-quotients
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

The action of [short maps](metric-spaces.short-maps-metric-spaces.md) on
[metric spaces](metric-spaces.metric-spaces.md) preserves
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : short-map-Metric-Space X Y)
  where

  map-short-map-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space X →
    cauchy-approximation-Metric-Space Y
  map-short-map-cauchy-approximation-Metric-Space =
    map-short-map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space X)
      ( pseudometric-Metric-Space Y)
      ( f)
```

## Properties

### Short maps preserve similarity in the Cauchy pseudocompletion of a pseudometric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : short-map-Metric-Space X Y)
  where abstract

  preserves-sim-short-map-cauchy-pseudocompletion-Metric-Space :
    preserves-sim-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space X)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space Y)
      ( map-short-map-cauchy-approximation-Metric-Space X Y f)
  preserves-sim-short-map-cauchy-pseudocompletion-Metric-Space {x} {y} =
    preserves-sim-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space X)
      ( pseudometric-Metric-Space Y)
      ( f)
      { x}
      { y}
```
