# Negation on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-negation-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[Addition on the real numbers](real-numbers.addition-real-numbers.md) is a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
abstract
  modulus-of-continuity-neg-ℝ : ℚ⁺ → ℚ⁺
  modulus-of-continuity-neg-ℝ = id

  is-modulus-of-uniform-continuity-modulus-of-continuity-neg-ℝ :
    {l : Level} →
    is-modulus-of-uniform-continuity-Metric-Space
      ( metric-space-leq-ℝ l)
      ( metric-space-leq-ℝ l)
      ( neg-ℝ)
      ( modulus-of-continuity-neg-ℝ)
  is-modulus-of-uniform-continuity-modulus-of-continuity-neg-ℝ
    a ε⁺@(ε , _) a' a~a' =
      neighborhood-abs-diff-bound-leq-ℝ
        ( ε⁺)
        ( neg-ℝ a)
        ( neg-ℝ a')
        ( inv-tr
          ( λ x → leq-ℝ x (real-ℚ ε))
          ( equational-reasoning
            abs-ℝ (neg-ℝ a -ℝ neg-ℝ a')
            ＝ abs-ℝ (neg-ℝ (a -ℝ a'))
              by ap abs-ℝ (inv (distributive-neg-add-ℝ _ _))
            ＝ abs-ℝ (a -ℝ a') by abs-neg-ℝ _)
          ( abs-diff-bound-neighborhood-leq-ℝ ε⁺ a a' a~a'))

  is-uniformly-continuous-neg-ℝ :
    {l : Level} →
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-leq-ℝ l)
      ( metric-space-leq-ℝ l)
      ( neg-ℝ)
  is-uniformly-continuous-neg-ℝ =
    intro-exists
      ( modulus-of-continuity-neg-ℝ)
      ( is-modulus-of-uniform-continuity-modulus-of-continuity-neg-ℝ)
```
