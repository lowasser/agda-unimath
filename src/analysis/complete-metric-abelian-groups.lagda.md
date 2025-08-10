# Complete metric Abelian groups

```agda
module analysis.complete-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A {{#concept "complete metric abelian group"}} is an
[abelian group](group-theory.abelian-groups.md) endowed with a
[metric structure](metric-spaces.metric-spaces.md) that forms a
[complete metric space](metric-spaces.complete-metric-spaces.md), in which the
addition operation on the abelian group is
[uniformly continuous](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
in each argument.

## Definition

```agda
Complete-Metric-Ab : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Complete-Metric-Ab l1 l2 =
  Σ ( Ab l1)
    ( λ G →
      Σ ( Metric-Structure l2 (type-Ab G))
        ( λ M →
          is-complete-Metric-Space (type-Ab G , M) ×
          ( (a : type-Ab G) →
            is-uniformly-continuous-function-Metric-Space
              ( type-Ab G , M)
              ( type-Ab G , M)
              ( add-Ab G a))))

module _
  {l1 l2 : Level} (G : Complete-Metric-Ab l1 l2)
  where

  ab-Complete-Metric-Ab : Ab l1
  ab-Complete-Metric-Ab = pr1 G

  type-Complete-Metric-Ab : UU l1
  type-Complete-Metric-Ab = type-Ab ab-Complete-Metric-Ab

  metric-structure-Complete-Metric-Ab :
    Metric-Structure l2 type-Complete-Metric-Ab
  metric-structure-Complete-Metric-Ab = pr1 (pr2 G)

  metric-space-Complete-Metric-Ab : Metric-Space l1 l2
  metric-space-Complete-Metric-Ab =
    ( type-Complete-Metric-Ab , metric-structure-Complete-Metric-Ab)

  is-complete-metric-space-Complete-Metric-Ab :
    is-complete-Metric-Space metric-space-Complete-Metric-Ab
  is-complete-metric-space-Complete-Metric-Ab = pr1 (pr2 (pr2 G))

  complete-metric-space-Complete-Metric-Ab : Complete-Metric-Space l1 l2
  complete-metric-space-Complete-Metric-Ab =
    ( metric-space-Complete-Metric-Ab ,
      is-complete-metric-space-Complete-Metric-Ab)
```

### Metric structure

```agda
  is-cauchy-sequence-Complete-Metric-Ab :
    sequence (type-Complete-Metric-Ab) → UU l2
  is-cauchy-sequence-Complete-Metric-Ab =
    is-cauchy-sequence-Metric-Space metric-space-Complete-Metric-Ab

  cauchy-sequence-Complete-Metric-Ab : UU (l1 ⊔ l2)
  cauchy-sequence-Complete-Metric-Ab =
    cauchy-sequence-Metric-Space metric-space-Complete-Metric-Ab

  limit-cauchy-sequence-Complete-Metric-Ab :
    cauchy-sequence-Complete-Metric-Ab → type-Complete-Metric-Ab
  limit-cauchy-sequence-Complete-Metric-Ab =
    limit-cauchy-sequence-Complete-Metric-Space
      ( complete-metric-space-Complete-Metric-Ab)
```
