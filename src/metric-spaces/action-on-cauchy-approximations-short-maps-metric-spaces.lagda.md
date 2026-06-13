# The action on Cauchy approximations of short maps on metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

The action of [short maps](metric-spaces.short-maps-metric-spaces.md) on
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
[metric spaces](metric-spaces.metric-spaces.md) is itself a
[short map](metric-spaces.short-maps-pseudometric-spaces.md) on the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md)
of the metric spaces.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : short-map-Metric-Space X Y)
  where

  short-map-cauchy-pseudocompletion-short-map-Metric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space X)
      ( cauchy-pseudocompletion-Metric-Space Y)
  short-map-cauchy-pseudocompletion-short-map-Metric-Space =
    short-map-cauchy-pseudocompletion-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space X)
      ( pseudometric-Metric-Space Y)
      ( f)

  map-short-map-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space X →
    cauchy-approximation-Metric-Space Y
  map-short-map-cauchy-approximation-Metric-Space =
    map-short-map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space X)
      ( pseudometric-Metric-Space Y)
      ( f)
```
