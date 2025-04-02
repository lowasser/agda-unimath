# The minimum function on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.products-metric-spaces
open import metric-spaces.uniformly-continuous-binary-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.maxima-minima-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.minimum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.uniformly-continuous-maximum-real-numbers
open import real-numbers.uniformly-continuous-negation-real-numbers
```

</details>

## Idea

[The minimum function on the real numbers](real-numbers.minimum-real-numbers.md)
is a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
abstract
  is-uniformly-continuous-min-ℝ :
    {l1 l2 : Level} →
    is-uniformly-continuous-binary-map-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( min-ℝ)
  is-uniformly-continuous-min-ℝ {l1} {l2} =
    inv-tr
      ( is-uniformly-continuous-map-Metric-Space
        ( product-Metric-Space (metric-space-leq-ℝ l1) ( metric-space-leq-ℝ l2))
        ( metric-space-leq-ℝ (l1 ⊔ l2)))
      ( eq-htpy
        ( λ (a , b) →
          equational-reasoning
            min-ℝ a b
            ＝ neg-ℝ (neg-ℝ (min-ℝ a b)) by inv (neg-neg-ℝ _)
            ＝ neg-ℝ (max-ℝ (neg-ℝ a) (neg-ℝ b)) by ap neg-ℝ (neg-min-ℝ _ _)))
      ( left-comp-uniformly-continuous-binary-map-Metric-Space
        ( metric-space-leq-ℝ l1)
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2))
        ( metric-space-leq-ℝ (l1 ⊔ l2))
        ( neg-ℝ)
        ( is-uniformly-continuous-neg-ℝ)
        ( λ a b → max-ℝ (neg-ℝ a) (neg-ℝ b))
        ( right-comp-uniformly-continuous-binary-map-Metric-Space
          ( metric-space-leq-ℝ l1)
          ( metric-space-leq-ℝ l1)
          ( metric-space-leq-ℝ l2)
          ( metric-space-leq-ℝ l2)
          ( metric-space-leq-ℝ (l1 ⊔ l2))
          ( max-ℝ)
          ( is-uniformly-continuous-max-ℝ)
          ( neg-ℝ)
          ( is-uniformly-continuous-neg-ℝ)
          ( neg-ℝ)
          ( is-uniformly-continuous-neg-ℝ)))
```
