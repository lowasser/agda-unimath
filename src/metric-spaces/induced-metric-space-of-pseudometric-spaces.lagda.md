# The induced metric space of a pseudometric space

```agda
module metric-spaces.induced-metric-space-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensional-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhoods
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Every [pseudometric space](metric-spaces.pseudometric-spaces.md) `M` induces a
[metric space](metric-spaces.metric-spaces.md) whose points are
[equivalence classes](foundation.equivalence-classes.md) of `M` by the
[similarity relation](metric-spaces.similarity-of-elements-pseudometric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  type-induced-metric-space-Pseudometric-Space : UU (l1 ⊔ lsuc l2)
  type-induced-metric-space-Pseudometric-Space =
    equivalence-class (equivalence-sim-Pseudometric-Space M)

  neighborhood-prop-induced-metric-space-Pseudometric-Space :
    Rational-Neighborhood-Relation
      ( l1 ⊔ l2)
      ( type-induced-metric-space-Pseudometric-Space)
  neighborhood-prop-induced-metric-space-Pseudometric-Space ε X Y =
    Π-Prop
      ( type-subtype-equivalence-class (equivalence-sim-Pseudometric-Space M) X)
      ( λ (x , x∈X) →
        Π-Prop
          ( type-subtype-equivalence-class
            ( equivalence-sim-Pseudometric-Space M)
            ( Y))
          ( λ (y , y∈Y) → neighborhood-prop-Pseudometric-Space M ε x y))

  neighborhood-induced-metric-space-Pseudometric-Space :
    ℚ⁺ → Relation (l1 ⊔ l2) type-induced-metric-space-Pseudometric-Space
  neighborhood-induced-metric-space-Pseudometric-Space ε X Y =
    type-Prop (neighborhood-prop-induced-metric-space-Pseudometric-Space ε X Y)
```

## Properties

### The induced neighborhood relation is reflexive

```agda
  abstract
    refl-neighborhood-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x : type-induced-metric-space-Pseudometric-Space) →
      neighborhood-induced-metric-space-Pseudometric-Space d x x
    refl-neighborhood-induced-metric-space-Pseudometric-Space d X x y =
      equivalent-members-equivalence-class
        ( equivalence-sim-Pseudometric-Space M)
        ( X)
        ( x)
        ( y)
        ( d)
```

### The induced neighborhood relation is symmetric

```agda
  abstract
    symmetric-neighborhood-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-induced-metric-space-Pseudometric-Space) →
      neighborhood-induced-metric-space-Pseudometric-Space d x y →
      neighborhood-induced-metric-space-Pseudometric-Space d y x
    symmetric-neighborhood-induced-metric-space-Pseudometric-Space
      d X Y d⟨X,Y⟩ (y , y∈Y) (x , x∈X) =
        symmetric-neighborhood-Pseudometric-Space
          ( M)
          ( d)
          ( x)
          ( y)
          ( d⟨X,Y⟩ (x , x∈X) (y , y∈Y))
```

### The induced neighborhood relation is triangular

```agda
  abstract
    triangular-neighborhood-induced-metric-space-Pseudometric-Space :
      (X Y Z : type-induced-metric-space-Pseudometric-Space) (d₁ d₂ : ℚ⁺) →
      neighborhood-induced-metric-space-Pseudometric-Space d₂ Y Z →
      neighborhood-induced-metric-space-Pseudometric-Space d₁ X Y →
      neighborhood-induced-metric-space-Pseudometric-Space (d₁ +ℚ⁺ d₂) X Z
    triangular-neighborhood-induced-metric-space-Pseudometric-Space
      X Y Z d₁ d₂ d₂⟨Y,Z⟩ d₁⟨X,Y⟩ (x , x∈X) (z , z∈Z) =
        let
          open
            do-syntax-trunc-Prop
              ( neighborhood-prop-Pseudometric-Space M (d₁ +ℚ⁺ d₂) x z)
        in do
          (y , y∈Y) ←
            is-inhabited-subtype-equivalence-class
              ( equivalence-sim-Pseudometric-Space M)
              ( Y)
          triangular-neighborhood-Pseudometric-Space
            ( M)
            ( x)
            ( y)
            ( z)
            ( d₁)
            ( d₂)
            ( d₂⟨Y,Z⟩ (y , y∈Y) (z , z∈Z))
            ( d₁⟨X,Y⟩ (x , x∈X) (y , y∈Y))
```

### The induced neighborhood relation is saturated

```agda
  abstract
    saturated-neighborhood-induced-metric-space-Pseudometric-Space :
      (ε : ℚ⁺) (X Y : type-induced-metric-space-Pseudometric-Space) →
      ((δ : ℚ⁺) →
        neighborhood-induced-metric-space-Pseudometric-Space (ε +ℚ⁺ δ) X Y) →
      neighborhood-induced-metric-space-Pseudometric-Space ε X Y
    saturated-neighborhood-induced-metric-space-Pseudometric-Space
      ε X Y H (x , x∈X) (y , y∈Y) =
        saturated-neighborhood-Pseudometric-Space M ε x y
          ( λ δ → H δ (x , x∈X) (y , y∈Y))
```

### The induced pseudometric space

```agda
  pseudometric-structure-induced-metric-space-Pseudometric-Space :
    Pseudometric-Structure
      ( l1 ⊔ l2)
      ( type-induced-metric-space-Pseudometric-Space)
  pseudometric-structure-induced-metric-space-Pseudometric-Space =
    neighborhood-prop-induced-metric-space-Pseudometric-Space ,
    refl-neighborhood-induced-metric-space-Pseudometric-Space ,
    symmetric-neighborhood-induced-metric-space-Pseudometric-Space ,
    triangular-neighborhood-induced-metric-space-Pseudometric-Space ,
    saturated-neighborhood-induced-metric-space-Pseudometric-Space

  pseudometric-induced-metric-space-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pseudometric-induced-metric-space-Pseudometric-Space =
    type-induced-metric-space-Pseudometric-Space ,
    pseudometric-structure-induced-metric-space-Pseudometric-Space
```

### The induced pseudometric is tight and extensional

```agda
  abstract
    is-tight-pseudometric-induced-metric-space-Pseudometric-Space :
      is-tight-Pseudometric-Space
        pseudometric-induced-metric-space-Pseudometric-Space
    is-tight-pseudometric-induced-metric-space-Pseudometric-Space X Y X~Y =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( equivalence-class-Set (equivalence-sim-Pseudometric-Space M))
              ( X)
              ( Y))
      in do
        (x , X~class⟨x⟩) ←
          is-equivalence-class-equivalence-class
            ( equivalence-sim-Pseudometric-Space M)
            ( X)
        let
          x∈X =
            backward-implication
              ( X~class⟨x⟩ x)
              ( refl-sim-Pseudometric-Space M x)
        (y , y∈Y) ←
          is-inhabited-subtype-equivalence-class
            ( equivalence-sim-Pseudometric-Space M)
            ( Y)
        eq-share-common-element-equivalence-class
          ( equivalence-sim-Pseudometric-Space M)
          ( X)
          ( Y)
          ( intro-exists
            ( y)
            ( backward-implication
              ( X~class⟨x⟩ y)
              ( λ ε → X~Y ε (x , x∈X) (y , y∈Y)) ,
              y∈Y))

  is-extensional-pseudometric-induced-metric-space-Pseudometric-Space :
    is-extensional-Pseudometric-Space
      pseudometric-induced-metric-space-Pseudometric-Space
  is-extensional-pseudometric-induced-metric-space-Pseudometric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-induced-metric-space-Pseudometric-Space)
      ( is-tight-pseudometric-induced-metric-space-Pseudometric-Space)
```

### The induced metric space

```agda
  induced-metric-space-Pseudometric-Space :
    Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  induced-metric-space-Pseudometric-Space =
    make-Metric-Space
      ( type-induced-metric-space-Pseudometric-Space)
      ( neighborhood-prop-induced-metric-space-Pseudometric-Space)
      ( refl-neighborhood-induced-metric-space-Pseudometric-Space)
      ( symmetric-neighborhood-induced-metric-space-Pseudometric-Space)
      ( triangular-neighborhood-induced-metric-space-Pseudometric-Space)
      ( saturated-neighborhood-induced-metric-space-Pseudometric-Space)
      ( is-extensional-pseudometric-induced-metric-space-Pseudometric-Space)
```

### Mapping from the pseudometric space to the induced metric space

```agda
  map-induced-metric-space-Pseudometric-Space :
    type-Pseudometric-Space M → type-induced-metric-space-Pseudometric-Space
  map-induced-metric-space-Pseudometric-Space =
    class (equivalence-sim-Pseudometric-Space M)

  abstract
    neighborhood-map-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-Pseudometric-Space M d x y →
      neighborhood-induced-metric-space-Pseudometric-Space
        ( d)
        ( map-induced-metric-space-Pseudometric-Space x)
        ( map-induced-metric-space-Pseudometric-Space y)
    neighborhood-map-induced-metric-space-Pseudometric-Space
      d x y d⟨x,y⟩ (x' , x≈x') (y' , y≈y') =
        preserves-neighborhood-sim-Pseudometric-Space' M y≈y' d x'
          ( preserves-neighborhood-sim-Pseudometric-Space M x≈x' d y d⟨x,y⟩)
```

### The isometry from a pseudometric space to its induced metric space

```agda
  is-isometry-map-induced-metric-space-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-induced-metric-space-Pseudometric-Space)
      ( map-induced-metric-space-Pseudometric-Space)
  pr1 (is-isometry-map-induced-metric-space-Pseudometric-Space d x y)
    Ndxy (x' , x~x') (y' , y~y') =
      preserves-neighborhood-sim-Pseudometric-Space M x~x' d y'
        ( preserves-neighborhood-sim-Pseudometric-Space' M y~y' d x Ndxy)
  pr2 (is-isometry-map-induced-metric-space-Pseudometric-Space d x y) NdXY =
    NdXY
      ( inhabitant-subtype-class-equivalence-class
        ( equivalence-sim-Pseudometric-Space M) x)
      ( inhabitant-subtype-class-equivalence-class
        ( equivalence-sim-Pseudometric-Space M) y)

  isometry-map-induced-metric-space-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( M)
      ( pseudometric-induced-metric-space-Pseudometric-Space)
  isometry-map-induced-metric-space-Pseudometric-Space =
    map-induced-metric-space-Pseudometric-Space ,
    is-isometry-map-induced-metric-space-Pseudometric-Space
```

### The isometric equivalence between a metric space and the induced metric space of its pseudometric

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  abstract
    is-isometry-map-induced-metric-space-pseudometric-Metric-Space :
      is-isometry-Metric-Space
        ( M)
        ( induced-metric-space-Pseudometric-Space
          ( pseudometric-Metric-Space M))
        ( map-induced-metric-space-Pseudometric-Space
          ( pseudometric-Metric-Space M))
    is-isometry-map-induced-metric-space-pseudometric-Metric-Space =
      is-isometry-map-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M)

    map-subtype-inv-induced-metric-space-pseudometric-Metric-Space :
      ( X :
        type-induced-metric-space-Pseudometric-Space
          ( pseudometric-Metric-Space M)) →
      type-subtype-equivalence-class
        ( equivalence-sim-Metric-Space M)
        ( X)
    map-subtype-inv-induced-metric-space-pseudometric-Metric-Space X =
      let
        equiv-sim = equivalence-sim-Metric-Space M
        open
          do-syntax-trunc-Prop
            ( is-contr-Prop (type-subtype-equivalence-class equiv-sim X))
      in
        center
          ( do
            (x , X≃class⟨x⟩) ←
              is-equivalence-class-equivalence-class equiv-sim X
            let
              x∈X =
                backward-implication
                  ( X≃class⟨x⟩ x)
                  ( refl-sim-Metric-Space M x)
            ( ( x , x∈X) ,
              λ (y , y∈X) →
                eq-type-subtype
                  ( subtype-equivalence-class equiv-sim X)
                  ( eq-sim-Metric-Space M x y
                    ( equivalent-members-equivalence-class
                      ( equiv-sim)
                      ( X)
                      ( x , x∈X)
                      ( y , y∈X)))))

  map-inv-induced-metric-space-pseudometric-Metric-Space :
    ( X :
      type-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M)) →
    type-Metric-Space M
  map-inv-induced-metric-space-pseudometric-Metric-Space X =
    pr1 (map-subtype-inv-induced-metric-space-pseudometric-Metric-Space X)

  is-section-map-induced-metric-space-pseudometric-Metric-Space :
    is-section
      ( map-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M))
      map-inv-induced-metric-space-pseudometric-Metric-Space
  is-section-map-induced-metric-space-pseudometric-Metric-Space X =
    let
      (x' , x'∈X) =
        map-subtype-inv-induced-metric-space-pseudometric-Metric-Space X
      X' =
        map-induced-metric-space-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( x')
    in
      eq-share-common-element-equivalence-class
        ( equivalence-sim-Metric-Space M)
        ( X')
        ( X)
        ( intro-exists
          ( x')
          ( refl-sim-Metric-Space M x' , x'∈X))

  is-retraction-map-induced-metric-space-pseudometric-Metric-Space :
    is-retraction
      ( map-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M))
      map-inv-induced-metric-space-pseudometric-Metric-Space
  is-retraction-map-induced-metric-space-pseudometric-Metric-Space x =
    let
      (x' , x~x') =
        map-subtype-inv-induced-metric-space-pseudometric-Metric-Space
          ( map-induced-metric-space-Pseudometric-Space
            ( pseudometric-Metric-Space M)
            ( x))
    in inv (eq-sim-Metric-Space M x x' x~x')

  is-equiv-map-induced-metric-space-pseudometric-Metric-Space :
    is-equiv
      ( map-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M))
  is-equiv-map-induced-metric-space-pseudometric-Metric-Space =
    is-equiv-is-invertible
      ( map-inv-induced-metric-space-pseudometric-Metric-Space)
      ( is-section-map-induced-metric-space-pseudometric-Metric-Space)
      ( is-retraction-map-induced-metric-space-pseudometric-Metric-Space)

  equiv-map-induced-metric-space-pseudometric-Metric-Space :
    type-Metric-Space M ≃
    type-induced-metric-space-Pseudometric-Space (pseudometric-Metric-Space M)
  equiv-map-induced-metric-space-pseudometric-Metric-Space =
    map-induced-metric-space-Pseudometric-Space
      ( pseudometric-Metric-Space M) ,
    is-equiv-map-induced-metric-space-pseudometric-Metric-Space

  isometric-equiv-induced-metric-space-pseudometric-Metric-Space :
    isometric-equiv-Metric-Space
      ( M)
      ( induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M))
  isometric-equiv-induced-metric-space-pseudometric-Metric-Space =
    equiv-map-induced-metric-space-pseudometric-Metric-Space ,
    is-isometry-map-induced-metric-space-pseudometric-Metric-Space
```
