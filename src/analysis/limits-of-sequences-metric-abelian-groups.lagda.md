# Limits of sequences in metric abelian groups

```agda
module analysis.limits-of-sequences-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="in a metric abelian group" Agda=is-limit-sequence-Metric-Ab}}
of a [sequence](lists.sequences.md) in a
[metric abelian group](analysis.metric-abelian-groups.md) is a
[limit](metric-spaces.limits-of-sequences-metric-spaces.md) of the sequence in
the underlying [metric space](metric-spaces.metric-spaces.md) of the group.

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (u : sequence (type-Metric-Ab G))
  (lim : type-Metric-Ab G)
  where

  is-limit-modulus-prop-sequence-Metric-Ab : (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-sequence-Metric-Ab =
    is-limit-modulus-prop-sequence-Metric-Space (metric-space-Metric-Ab G) u lim

  is-limit-modulus-sequence-Metric-Ab : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Metric-Ab m =
    type-Prop (is-limit-modulus-prop-sequence-Metric-Ab m)

  is-limit-prop-sequence-Metric-Ab : Prop l2
  is-limit-prop-sequence-Metric-Ab =
    is-limit-prop-sequence-Metric-Space (metric-space-Metric-Ab G) u lim

  is-limit-sequence-Metric-Ab : UU l2
  is-limit-sequence-Metric-Ab = type-Prop is-limit-prop-sequence-Metric-Ab
```
