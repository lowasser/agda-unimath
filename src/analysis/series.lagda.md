# Series

```agda
module analysis.series where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "series" WDID=Q170198 WD="series" Agda=series-Ring-In-Metric-Space}}
is an infinite sum of terms in a
[complete metric abelian group](analysis.complete-metric-abelian-groups.md).

## Definition

```agda
record series {l1 l2 : Level} (G : Complete-Metric-Ab l1 l2) : UU l1 where
  field
    terms-series : sequence (type-Complete-Metric-Ab G)

open series
```

## Properties

### Partial sums

```agda
module _
  {l1 l2 : Level} {G : Complete-Metric-Ab l1 l2} (S : series G)
  where

  partial-sum-series : sequence (type-Complete-Metric-Ab G)
  partial-sum-series n =
    sum-fin-sequence-type-Ab
      ( ab-Complete-Metric-Ab G)
      ( n)
      ( λ i → terms-series S (nat-Fin n i))
```

### Convergence

```agda
  converges-series : UU l2
  converges-series =
    is-cauchy-sequence-Complete-Metric-Ab G partial-sum-series

convergent-series :
  {l1 l2 : Level} (G : Complete-Metric-Ab l1 l2) → UU (l1 ⊔ l2)
convergent-series G = Σ (series G) converges-series

sum-convergent-series :
  {l1 l2 : Level} (G : Complete-Metric-Ab l1 l2) (S : convergent-series G) →
  type-Complete-Metric-Ab G
sum-convergent-series G (S , converges-S) =
  limit-cauchy-sequence-Complete-Metric-Ab
    ( G)
    ( partial-sum-series S , converges-S)
```
