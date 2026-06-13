# Addition of Cauchy real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-cauchy-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import analysis.metric-abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-additive-group-of-rational-numbers

open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.cauchy-real-numbers
```

</details>

## Idea

## Definition

```agda
metric-ab-add-cauchy-ℝ : Metric-Ab lzero lzero
metric-ab-add-cauchy-ℝ =
  metric-ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

ab-add-cauchy-ℝ : Ab lzero
ab-add-cauchy-ℝ = ab-Metric-Ab metric-ab-add-cauchy-ℝ

add-cauchy-ℝ : cauchy-ℝ → cauchy-ℝ → cauchy-ℝ
add-cauchy-ℝ = add-Ab ab-add-cauchy-ℝ
```

## Properties

### Abelian group properties of addition
