# Differentiable maps from proper closed intervals on ℝ to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import linear-algebra.normed-real-vector-spaces
open import foundation.subtypes
open import real-numbers.inequality-real-numbers
open import lists.sequences
open import real-numbers.difference-real-numbers
open import foundation.existential-quantification
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.accumulation-points-subsets-real-numbers
open import real-numbers.multiplication-real-numbers
open import foundation.propositions
open import real-numbers.distance-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import foundation.function-types
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.universe-levels
open import real-numbers.proper-closed-intervals-real-numbers
open import elementary-number-theory.positive-rational-numbers
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    subtype (lsuc l1) (ℚ⁺ → ℚ⁺)
  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    μ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( λ (x , x∈[a,b]) →
            Π-Prop
              ( type-proper-closed-interval-ℝ l1 [a,b])
              ( λ (y , y∈[a,b]) →
                hom-Prop
                  ( neighborhood-prop-ℝ l1 (μ ε) x y)
                  ( leq-prop-ℝ
                    ( dist-Normed-ℝ-Vector-Space V
                      ( diff-Normed-ℝ-Vector-Space V
                        ( f (y , y∈[a,b]))
                        ( f (x , x∈[a,b])))
                      ( mul-Normed-ℝ-Vector-Space V (y -ℝ x) (g (x , x∈[a,b]))))
                    ( real-ℚ⁺ ε *ℝ dist-ℝ y x)))))

  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (ℚ⁺ → ℚ⁺) → UU (lsuc l1)
  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    Prop (lsuc l1)
  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-inhabited-subtype-Prop
      ( is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1)
  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    type-Prop
      ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V) →
    UU (lsuc l1 ⊔ l2)
  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space f =
    Σ ( type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
      ( is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f))

  differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1 ⊔ l2)
  differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    Σ ( type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
      ( is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space →
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space = pr1

  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space →
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    pr1 ∘ pr2

  is-derivative-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (f : differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space) →
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( f))
      ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( f))
  is-derivative-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    pr2 ∘ pr2
```

## Properties

### Proving the derivative of a map from a modulus

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where abstract

  is-derivative-modulus-of-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    ( (ε : ℚ⁺) →
      Σ ( ℚ⁺)
        ( λ δ →
          (x y : type-proper-closed-interval-ℝ l1 [a,b]) →
          neighborhood-ℝ l1 δ (pr1 x) (pr1 y) →
          leq-ℝ
            ( dist-Normed-ℝ-Vector-Space V
              ( diff-Normed-ℝ-Vector-Space V (f y) (f x))
              ( mul-Normed-ℝ-Vector-Space V (pr1 y -ℝ pr1 x) (g x)))
            ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 y) (pr1 x)))) →
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( g)
  is-derivative-modulus-of-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    M =
    intro-exists (pr1 ∘ M) (pr2 ∘ M)
```

### If `g` is a derivative of `f`, and `aₙ` is a sequence accumulating to `x`, and the limit exists, then `g x` is equal to the limit of `(f aₙ - f x)/(aₙ - x)` as `n → ∞`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  ((x , x∈[a,b]) : type-proper-closed-interval-ℝ l1 [a,b])
  (y@(sequence-y , _) :
    sequence-accumulating-to-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( x))
  where

  sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    sequence (type-Normed-ℝ-Vector-Space V)
  sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
    n =
    mul-Normed-ℝ-Vector-Space
      ( V)
      ( real-inv-nonzero-ℝ
        ( nonzero-diff-apart-ℝ
          ( real-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( x)
            ( y)
            ( n))
          ( x)
          ( apart-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( x)
            ( y)
            ( n))))
      ( diff-Normed-ℝ-Vector-Space V
        ( f (sequence-y n))
        ( f (x , x∈[a,b])))
```
