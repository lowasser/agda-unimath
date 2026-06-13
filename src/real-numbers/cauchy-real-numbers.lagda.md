# The Cauchy real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cauchy-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-additive-group-of-rational-numbers
open import analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.binary-relations
open import foundation.embeddings
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

The {{#concept "Cauchy real numbers" Agda=cauchy-ℝ}} are the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md) of
the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md)
of the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

Note that constructively, the Cauchy real numbers are not themselves
[complete](metric-spaces.complete-metric-spaces.md). As a result, the
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) are instead the
standard definition of ℝ.

## Definition

```agda
metric-space-cauchy-ℝ : Metric-Space lzero lzero
metric-space-cauchy-ℝ =
  metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

set-cauchy-ℝ : Set lzero
set-cauchy-ℝ = set-Metric-Space metric-space-cauchy-ℝ

cauchy-ℝ : UU lzero
cauchy-ℝ = type-Set set-cauchy-ℝ

neighborhood-prop-cauchy-ℝ : Rational-Neighborhood-Relation lzero cauchy-ℝ
neighborhood-prop-cauchy-ℝ =
  neighborhood-prop-Metric-Space metric-space-cauchy-ℝ

neighborhood-cauchy-ℝ : ℚ⁺ → Relation lzero cauchy-ℝ
neighborhood-cauchy-ℝ =
  neighborhood-Metric-Space metric-space-cauchy-ℝ
```

### The map from the rational numbers to the Cauchy real numbers

```agda
isometry-cauchy-real-ℚ :
  isometry-Metric-Space metric-space-ℚ metric-space-cauchy-ℝ
isometry-cauchy-real-ℚ =
  isometry-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

emb-cauchy-real-ℚ : ℚ ↪ cauchy-ℝ
emb-cauchy-real-ℚ =
  emb-map-isometry-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-cauchy-ℝ)
    ( isometry-cauchy-real-ℚ)

cauchy-real-ℚ : ℚ → cauchy-ℝ
cauchy-real-ℚ = map-emb emb-cauchy-real-ℚ
```

### Important Cauchy real numbers

```agda
zero-cauchy-ℝ : cauchy-ℝ
zero-cauchy-ℝ = cauchy-real-ℚ zero-ℚ

one-cauchy-ℝ : cauchy-ℝ
one-cauchy-ℝ = cauchy-real-ℚ one-ℚ
```
