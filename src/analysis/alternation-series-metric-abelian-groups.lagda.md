# The alternation of series in metric abelian groups

```agda
module analysis.alternation-series-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.alternation-sequences-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "alternation" Disambiguation="of a series in a metric abelian group" Agda=alternation-series-Metric-Ab}}
of a [series](analysis.series-metric-abelian-groups.md) `∑ aₙ` in a
[metric abelian group](analysis.metric-abelian-groups.md) is the series `∑ bₙ`
where the sequence `bₙ` is the
[alternation](analysis.alternation-sequences-metric-abelian-groups.md) of the
sequence `aₙ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {G : Metric-Ab l1 l2}
  where

  alternation-series-Metric-Ab : series-Metric-Ab G → series-Metric-Ab G
  alternation-series-Metric-Ab (series-terms-Metric-Ab u) =
    series-terms-Metric-Ab (alternation-sequence-Metric-Ab G u)
```
