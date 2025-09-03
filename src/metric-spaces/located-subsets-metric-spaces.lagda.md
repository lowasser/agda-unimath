# Located subsets of metric spaces

```agda
module metric-spaces.located-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import real-numbers.infima-families-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A [subset](metric-spaces.subspaces-metric-spaces.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is
{{#concept "located" Disambiguation="subset of a metric space" Agda=is-located-subset-Metric-Space}}
if for all `x : X`, the set of `d` such that there is an `s ∈ S` where `x` and
`s` are in a `d`-neighborhood of each other has an
[infimum](real-numbers.infima-families-real-numbers.md) in the real numbers.

This is a distinct notion from being
[located](metric-spaces.located-metric-spaces.md) as a subspace of `X`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (l4 : Level) (X : Metric-Space l1 l2)
  (S : subset-Metric-Space l3 X)
  where

  is-located-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  is-located-prop-subset-Metric-Space =
    let
      R : type-Metric-Space X → subtype (l1 ⊔ l2 ⊔ l3) ℚ⁺
      R x d =
        intersect-prop-subtype
          ( S)
          ( neighborhood-prop-Metric-Space X d x)
    in
      Π-Prop
        ( type-Metric-Space X)
        ( λ x →
          has-infimum-prop-family-ℝ
            ( real-ℚ⁺ ∘ inclusion-subtype (R x))
            ( l4))

  is-located-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  is-located-subset-Metric-Space =
    type-Prop is-located-prop-subset-Metric-Space
```
