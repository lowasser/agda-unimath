# The absolute value function on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.uniformly-continuous-binary-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.uniformly-continuous-maximum-real-numbers
open import real-numbers.uniformly-continuous-negation-real-numbers
```

</details>

## Idea

[The absolute value function on the real numbers](real-numbers.absolute-value-real-numbers.md)
is a
[uniformly continuous function](metric-spaces.uniformly-continuous-functions-metric-spaces.md)

## Proof

```agda
opaque
  unfolding abs-ℝ

  is-uniformly-continuous-abs-ℝ :
    {l : Level} →
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-leq-ℝ l)
      ( metric-space-leq-ℝ l)
      ( abs-ℝ)
  is-uniformly-continuous-abs-ℝ {l} =
    diagonal-uniformly-continuous-binary-map-Metric-Space
      ( metric-space-leq-ℝ l)
      ( metric-space-leq-ℝ l)
      ( λ x y → max-ℝ x (neg-ℝ y))
      ( right-comp-uniformly-continuous-binary-map-Metric-Space
        ( metric-space-leq-ℝ l)
        ( metric-space-leq-ℝ l)
        ( metric-space-leq-ℝ l)
        ( metric-space-leq-ℝ l)
        ( metric-space-leq-ℝ l)
        ( max-ℝ)
        ( is-uniformly-continuous-max-ℝ)
        ( id)
        ( is-uniformly-continuous-map-id-Metric-Space (metric-space-leq-ℝ l))
        ( neg-ℝ)
        ( is-uniformly-continuous-neg-ℝ))
```
