# Metric quotients of Cauchy pseudocompletions of metric abelian groups

```agda
module analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of the
[Cauchy pseudocompletion](analysis.cauchy-pseudocompletions-metric-abelian-groups.md)
of a [metric abelian group](analysis.metric-abelian-groups.md) forms a
[metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    metric-quotient-Pseudometric-Space (cauchy-pseudocompletion-Metric-Ab G)

  set-metric-quotient-cauchy-pseudocompletion-Metric-Ab : Set (l1 ⊔ l2)
  set-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    set-Metric-Space metric-quotient-cauchy-pseudocompletion-Metric-Ab

  type-metric-quotient-cauchy-pseudocompletion-Metric-Ab : UU (l1 ⊔ l2)
  type-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    type-Set set-metric-quotient-cauchy-pseudocompletion-Metric-Ab

  neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Rational-Neighborhood-Relation
      ( l1 ⊔ l2)
      ( type-metric-quotient-cauchy-pseudocompletion-Metric-Ab)
  neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-prop-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab)

  neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    ℚ⁺ →
    Relation (l1 ⊔ l2) type-metric-quotient-cauchy-pseudocompletion-Metric-Ab
  neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab)
```
