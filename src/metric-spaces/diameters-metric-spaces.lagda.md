# Diameters of metric spaces

```agda
module metric-spaces.diameters-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import real-numbers.metric-space-of-real-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.uniformly-continuous-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous
open import metric-spaces.metrics-of-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

If a [metric space](metric-spaces.metric-spaces.md) `X` has a
[metric](metric-spaces.metrics-of-metric-spaces.md) `ρ`, then a
{{#concept "diameter" disambiguation="of a metric space" Agda=is-diameter-Metric-Space}}
`d` of `M` is a [supremum](real-numbers.suprema-families-real-numbers.md) of
`ρ x y` for all `x y : X`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space X))
  (H : is-metric-of-Metric-Space X ρ)
  where

  is-diameter-prop-Metric-Space : {l4 : Level} → ℝ⁰⁺ l4 → Prop (l1 ⊔ l3 ⊔ l4)
  is-diameter-prop-Metric-Space d =
    is-supremum-prop-family-ℝ
      ( real-ℝ⁰⁺ ∘ ind-Σ ρ)
      ( real-ℝ⁰⁺ d)

  is-diameter-Metric-Space : {l4 : Level} → ℝ⁰⁺ l4 → UU (l1 ⊔ l3 ⊔ l4)
  is-diameter-Metric-Space d = type-Prop (is-diameter-prop-Metric-Space d)

  has-diameter-prop-Metric-Space : (l4 : Level) → Prop (l1 ⊔ l3 ⊔ lsuc l4)
  has-diameter-prop-Metric-Space =
    has-supremum-prop-family-ℝ (real-ℝ⁰⁺ ∘ ind-Σ ρ)

  has-diameter-Metric-Space : (l4 : Level) → UU (l1 ⊔ l3 ⊔ lsuc l4)
  has-diameter-Metric-Space l4 = type-Prop (has-diameter-prop-Metric-Space l4)
```

## Properties

### Inhabited, totally bounded subspaces of metric spaces have a diameter

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space X))
  (H : is-metric-of-Metric-Space X ρ)
  (S : inhabited-totally-bounded-subspace-Metric-Space l3 l4 X)
  where

  has-diameter-inhabited-totally-bounded-subspace-Metric-Space :
    has-diameter-Metric-Space
      ( subspace-inhabited-totally-bounded-subspace-Metric-Space X S)
      ( λ (s , s∈S) (t , t∈S) → ρ s t)
      ( λ ε (s , s∈S) (t , t∈S) → H ε s t)
      {!  !}
  has-diameter-inhabited-totally-bounded-subspace-Metric-Space =
    let
      S' = subspace-inhabited-totally-bounded-subspace-Metric-Space X S
      ρ' : distance-function l3 (set-Metric-Space S')
      ρ' = λ (s , s∈S) (t , t∈S) → ρ s t
      is-metric-ρ' = λ ε (s , s∈S) (t , t∈S) → H ε s t
      D :
        inhabited-totally-bounded-subset-ℝ (l1 ⊔ lsuc l3) l3 (l1 ⊔ lsuc l3 ⊔ l4)
      D =
        im-uniformly-continuous-function-inhabited-totally-bounded-subspace-Metric-Space
          ( product-Metric-Space X X)
          ( metric-space-ℝ l3)
          ( comp-uniformly-continuous-function-Metric-Space
            ( product-Metric-Space X X)
            ( metric-space-ℝ⁰⁺ l3)
            ( metric-space-ℝ l3)
            ( uniformly-continuous-inclusion-subspace-Metric-Space
              ( metric-space-ℝ l3)
              ( is-nonnegative-prop-ℝ))
            ( uniformly-continuous-metric-of-Metric-Space X ρ H))
          ( product-inhabited-totally-bounded-subspace-Metric-Space X X S S)
      (sup-D , is-sup-D) =
        has-supremum-inhabited-totally-bounded-subset-ℝ D
    in
      ( sup-D ,
        ( λ ((s , s∈S) , (t , t∈S)) →
          {! is-upper-bound-is-supremum-family-ℝ (real-ℝ⁰⁺ ∘ ind-Σ ρ ∘ ?) sup-D is-sup-D ?  !}) ,
        {!   !})
```
