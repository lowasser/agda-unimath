# The pseudometric space of Cauchy approximations in metric spaces

```agda
module metric-spaces.pseudometric-space-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

For any [metric space](metric-spaces.metric-spaces.md) `M`, there is a
[pseudometric space](metric-spaces.pseudometric-spaces.md) of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M`, whose neighborhood relation defines that two Cauchy approximations `x` and
`y` are in a `d`-neighborhood of one another if for all `δ ε θ : ℚ⁺`, `x δ` and
`y θ` are in a `(δ + ε + θ + d)`-neighborhood of one another in `M`.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  neighborhood-prop-pseudometric-cauchy-approximation-Metric-Space :
    Rational-Neighborhood-Relation l2 (cauchy-approximation-Metric-Space M)
  neighborhood-prop-pseudometric-cauchy-approximation-Metric-Space
    d x y =
      Π-Prop
        ( ℚ⁺)
        ( λ δ →
          Π-Prop
            ( ℚ⁺)
            ( λ ε →
              neighborhood-prop-Metric-Space
                ( M)
                ( δ +ℚ⁺ ε +ℚ⁺ d)
                ( map-cauchy-approximation-Metric-Space M x δ)
                ( map-cauchy-approximation-Metric-Space M y ε)))

  neighborhood-pseudometric-cauchy-approximation-Metric-Space :
    ℚ⁺ → Relation l2 (cauchy-approximation-Metric-Space M)
  neighborhood-pseudometric-cauchy-approximation-Metric-Space d x y =
    type-Prop
      ( neighborhood-prop-pseudometric-cauchy-approximation-Metric-Space
        ( d)
        ( x)
        ( y))
```

## Properties

### The neighborhood relation is reflexive

```agda
  abstract
    refl-neighborhood-pseudometric-cauchy-approximation-Metric-Space :
      (d : ℚ⁺) (x : cauchy-approximation-Metric-Space M) →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space d x x
    refl-neighborhood-pseudometric-cauchy-approximation-Metric-Space d x δ ε =
      let
        xδ = map-cauchy-approximation-Metric-Space M x δ
        xε = map-cauchy-approximation-Metric-Space M x ε
      in
        monotonic-neighborhood-Metric-Space M xδ xε
          ( δ +ℚ⁺ ε)
          ( δ +ℚ⁺ ε +ℚ⁺ d)
          ( le-right-add-rational-ℚ⁺ _ d)
          ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
            ( M)
            ( x)
            ( δ)
            ( ε))
```

### The neighborhood relation is symmetric

```agda
    symmetric-neighborhood-pseudometric-cauchy-approximation-Metric-Space :
      (d : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space d x y →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space d y x
    symmetric-neighborhood-pseudometric-cauchy-approximation-Metric-Space
      d x y Ndxy δ ε =
        let
          xε = map-cauchy-approximation-Metric-Space M x ε
          yδ = map-cauchy-approximation-Metric-Space M y δ
        in
          tr
            ( λ d' → neighborhood-Metric-Space M d' yδ xε)
            ( ap (_+ℚ⁺ d) (commutative-add-ℚ⁺ ε δ))
            ( symmetric-neighborhood-Metric-Space M _ xε yδ (Ndxy ε δ))
```

### The neighborhood relation is triangular

```agda
    triangular-neighborhood-pseudometric-cauchy-approximation-Metric-Space :
      (x y z : cauchy-approximation-Metric-Space M) →
      (dxy dyz : ℚ⁺) →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space dyz y z →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space dxy x y →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space
        ( dxy +ℚ⁺ dyz)
        ( x)
        ( z)
    triangular-neighborhood-pseudometric-cauchy-approximation-Metric-Space
      x y z dxy dyz Ndyz Ndxy δ ε =
        let
          xδ = map-cauchy-approximation-Metric-Space M x δ
          zε = map-cauchy-approximation-Metric-Space M z ε
        in
        saturated-neighborhood-Metric-Space M (δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz)) xδ zε
          ( λ θ →
            let
              (θ₂ , θ₂+θ₂<θ) = bound-double-le-ℚ⁺ θ
              (θa , θb , θa+θb=θ₂) = split-ℚ⁺ θ₂
              yθa = map-cauchy-approximation-Metric-Space M y θa
            in
              monotonic-neighborhood-Metric-Space
                ( M)
                ( xδ)
                ( zε)
                ( (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb))
                ( δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz) +ℚ⁺ θ)
                ( tr
                  ( λ q → le-ℚ⁺ q (δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz) +ℚ⁺ θ))
                  ( equational-reasoning
                    ((δ +ℚ⁺ ε) +ℚ⁺ (dxy +ℚ⁺ dyz)) +ℚ⁺ (θ₂ +ℚ⁺ θ₂)
                    ＝
                      ((δ +ℚ⁺ dxy) +ℚ⁺ (ε +ℚ⁺ dyz)) +ℚ⁺
                      ((θa +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( interchange-law-add-add-ℚ⁺ δ ε dxy dyz)
                          ( inv (ap-add-ℚ⁺ θa+θb=θ₂ θa+θb=θ₂))
                    ＝
                      ((δ +ℚ⁺ dxy) +ℚ⁺ (θa +ℚ⁺ θb)) +ℚ⁺
                      ((ε +ℚ⁺ dyz) +ℚ⁺ (θa +ℚ⁺ θb))
                      by interchange-law-add-add-ℚ⁺ _ _ _ _
                    ＝
                      ((δ +ℚ⁺ θa) +ℚ⁺ (dxy +ℚ⁺ θb)) +ℚ⁺
                      ((ε +ℚ⁺ θa) +ℚ⁺ (dyz +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( interchange-law-add-add-ℚ⁺ _ _ _ _)
                          ( interchange-law-add-add-ℚ⁺ _ _ _ _)
                    ＝
                      (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺
                      ((θa +ℚ⁺ ε) +ℚ⁺ (dyz +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( inv (associative-add-ℚ⁺ _ _ _))
                          ( ap-add-ℚ⁺ (commutative-add-ℚ⁺ _ _) refl)
                    ＝ (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                      by ap-add-ℚ⁺ refl (inv (associative-add-ℚ⁺ _ _ _)))
                  ( preserves-le-right-add-ℚ⁺
                    ( δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz))
                    ( θ₂ +ℚ⁺ θ₂)
                    ( θ)
                    ( θ₂+θ₂<θ)))
                ( triangular-neighborhood-Metric-Space M xδ yθa zε
                  ( δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb)
                  ( θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                  ( monotonic-neighborhood-Metric-Space M yθa zε
                    ( θa +ℚ⁺ ε +ℚ⁺ dyz)
                    ( θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                    ( le-left-add-ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz) θb)
                    ( Ndyz θa ε))
                  ( monotonic-neighborhood-Metric-Space M xδ yθa
                    ( δ +ℚ⁺ θa +ℚ⁺ dxy)
                    ( δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb)
                    ( le-left-add-ℚ⁺ (δ +ℚ⁺ θa +ℚ⁺ dxy) θb)
                    ( Ndxy δ θa))))
```

### The neighborhood relation is saturated

```agda
    saturated-neighborhood-pseudometric-cauchy-approximation-Metric-Space :
      (ε : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
      ( (δ : ℚ⁺) →
        neighborhood-pseudometric-cauchy-approximation-Metric-Space
          ( ε +ℚ⁺ δ)
          ( x)
          ( y)) →
      neighborhood-pseudometric-cauchy-approximation-Metric-Space ε x y
    saturated-neighborhood-pseudometric-cauchy-approximation-Metric-Space
      d x y H δ ε =
        let
          xδ = map-cauchy-approximation-Metric-Space M x δ
          yε = map-cauchy-approximation-Metric-Space M y ε
        in
          saturated-neighborhood-Metric-Space M
            ( δ +ℚ⁺ ε +ℚ⁺ d)
            ( xδ)
            ( yε)
            ( λ θ →
              tr
                ( λ η → neighborhood-Metric-Space M η xδ yε)
                ( inv (associative-add-ℚ⁺ _ _ _))
                ( H θ δ ε))
```

### The pseudometric space of Cauchy approximations

```agda
  structure-pseudometric-cauchy-approximation-Metric-Space :
    Pseudometric-Structure l2 (cauchy-approximation-Metric-Space M)
  structure-pseudometric-cauchy-approximation-Metric-Space =
    neighborhood-prop-pseudometric-cauchy-approximation-Metric-Space ,
    refl-neighborhood-pseudometric-cauchy-approximation-Metric-Space ,
    symmetric-neighborhood-pseudometric-cauchy-approximation-Metric-Space ,
    triangular-neighborhood-pseudometric-cauchy-approximation-Metric-Space ,
    saturated-neighborhood-pseudometric-cauchy-approximation-Metric-Space

  pseudometric-cauchy-approximation-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) l2
  pseudometric-cauchy-approximation-Metric-Space =
    cauchy-approximation-Metric-Space M ,
    structure-pseudometric-cauchy-approximation-Metric-Space
```

### The isometry from a metric space to the pseudometric space of its Cauchy approximations

```agda
  map-pseudometric-cauchy-approximation-Metric-Space :
    type-Metric-Space M → cauchy-approximation-Metric-Space M
  map-pseudometric-cauchy-approximation-Metric-Space =
    const-cauchy-approximation-Metric-Space M

  map-neighborhood-pseudometric-cauchy-approximation-Metric-Space :
    (d : ℚ⁺) → (x y : type-Metric-Space M) →
    neighborhood-Metric-Space M d x y →
    neighborhood-pseudometric-cauchy-approximation-Metric-Space
      ( d)
      ( map-pseudometric-cauchy-approximation-Metric-Space x)
      ( map-pseudometric-cauchy-approximation-Metric-Space y)
  map-neighborhood-pseudometric-cauchy-approximation-Metric-Space
    d x y Ndxy δ ε =
      monotonic-neighborhood-Metric-Space M x y d (δ +ℚ⁺ ε +ℚ⁺ d)
        ( le-right-add-ℚ⁺ (δ +ℚ⁺ ε) d)
        ( Ndxy)

  abstract
    is-isometry-map-pseudometric-cauchy-approximation-Metric-Space :
      is-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( pseudometric-cauchy-approximation-Metric-Space)
        ( map-pseudometric-cauchy-approximation-Metric-Space)
    pr1 (is-isometry-map-pseudometric-cauchy-approximation-Metric-Space d x y)
      = map-neighborhood-pseudometric-cauchy-approximation-Metric-Space d x y
    pr2 (is-isometry-map-pseudometric-cauchy-approximation-Metric-Space d x y)
      Ndxy' =
        saturated-neighborhood-Metric-Space M d x y
          ( λ δ →
            let
              (δ₁ , δ₂ , δ₁+δ₂=δ) = split-ℚ⁺ δ
            in
              tr
                ( λ ε → neighborhood-Metric-Space M ε x y)
                ( commutative-add-ℚ⁺ _ _ ∙ ap (d +ℚ⁺_) δ₁+δ₂=δ)
                ( Ndxy' δ₁ δ₂))

  isometry-map-pseudometric-cauchy-approximation-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( pseudometric-cauchy-approximation-Metric-Space)
  isometry-map-pseudometric-cauchy-approximation-Metric-Space =
    map-pseudometric-cauchy-approximation-Metric-Space ,
    is-isometry-map-pseudometric-cauchy-approximation-Metric-Space
```
