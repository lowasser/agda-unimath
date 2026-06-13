# The Cauchy real numbers

```agda
module real-numbers.cauchy-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
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

Note that constructively, the Cauchy and
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) are not known to
coincide, and that the Dedekind real numbers are used as the standard definition
of the real numbers in agda-unimath.

## Definition

```agda
metric-space-cauchy-ℝ : Metric-Space lzero lzero
metric-space-cauchy-ℝ =
  metric-quotient-Pseudometric-Space
    ( cauchy-pseudocompletion-Metric-Space metric-space-ℚ)

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
