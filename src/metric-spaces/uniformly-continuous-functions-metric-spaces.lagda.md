# Uniformly continuous functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-ucont-function-Metric-Space}}
if there exists a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever
`x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of
`f x`. The function `m` is called a modulus of uniform continuity of `f`.

A
{{#concept "modulated uniformly continuous function" Disambiguation="function between metric spaces" Agda=modulated-ucont-function-Metric-Space}}
is a pair of a function `f` and a specific modulus of uniform continuity of `f`.

## Definitions

### The property of being a uniformly continuous function

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-function-Metric-Space m =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x →
        is-modulus-of-continuity-at-point-prop-function-Metric-Space
          X
          Y
          f
          x
          m)

  is-modulus-of-uniform-continuity-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-function-Metric-Space m =
    type-Prop (is-modulus-of-uniform-continuity-prop-function-Metric-Space m)

  modulus-of-uniform-continuity-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-function-Metric-Space =
    type-subtype is-modulus-of-uniform-continuity-prop-function-Metric-Space

  is-ucont-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-ucont-prop-function-Metric-Space =
    is-inhabited-subtype-Prop
      is-modulus-of-uniform-continuity-prop-function-Metric-Space

  is-ucont-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-ucont-function-Metric-Space =
    type-Prop is-ucont-prop-function-Metric-Space
```

### The type of uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  ucont-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  ucont-function-Metric-Space =
    type-subtype (is-ucont-prop-function-Metric-Space X Y)

  map-ucont-function-Metric-Space :
    ucont-function-Metric-Space →
    type-function-Metric-Space X Y
  map-ucont-function-Metric-Space = pr1

  is-ucont-map-ucont-function-Metric-Space :
    (f : ucont-function-Metric-Space) →
    is-ucont-function-Metric-Space X Y (map-ucont-function-Metric-Space f)
  is-ucont-map-ucont-function-Metric-Space = pr2
```

### The type of modulated uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  modulated-ucont-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  modulated-ucont-function-Metric-Space =
    Σ ( type-function-Metric-Space X Y)
      ( modulus-of-uniform-continuity-function-Metric-Space X Y)

  map-modulated-ucont-function-Metric-Space :
    modulated-ucont-function-Metric-Space →
    type-function-Metric-Space X Y
  map-modulated-ucont-function-Metric-Space = pr1

  modulus-modulated-ucont-function-Metric-Space :
    (f : modulated-ucont-function-Metric-Space) →
    modulus-of-uniform-continuity-function-Metric-Space
      ( X)
      ( Y)
      ( map-modulated-ucont-function-Metric-Space f)
  modulus-modulated-ucont-function-Metric-Space = pr2

trunc-modulated-ucont-function-Metric-Space :
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  modulated-ucont-function-Metric-Space X Y → ucont-function-Metric-Space X Y
trunc-modulated-ucont-function-Metric-Space _ _ (f , Mf) =
  ( f , unit-trunc-Prop Mf)
```

## Properties

### Uniformly continuous functions are continuous everywhere

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-continuous-at-point-is-ucont-function-Metric-Space :
    is-ucont-function-Metric-Space X Y f →
    (x : type-Metric-Space X) →
    is-continuous-at-point-function-Metric-Space X Y f x
  is-continuous-at-point-is-ucont-function-Metric-Space H x =
    elim-exists
      ( is-continuous-at-point-prop-function-Metric-Space X Y f x)
      ( λ m K → intro-exists m (K x))
      ( H)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  where

  is-ucont-comp-function-Metric-Space :
    (g : type-function-Metric-Space Y Z) →
    (f : type-function-Metric-Space X Y) →
    is-ucont-function-Metric-Space Y Z g →
    is-ucont-function-Metric-Space X Y f →
    is-ucont-function-Metric-Space X Z (g ∘ f)
  is-ucont-comp-function-Metric-Space g f H K =
    let
      open
        do-syntax-trunc-Prop
          ( is-ucont-prop-function-Metric-Space X Z (g ∘ f))
    in
      do
        mg , is-modulus-uniform-mg ← H
        mf , is-modulus-uniform-mf ← K
        intro-exists
          ( mf ∘ mg)
          ( λ x ε x' →
            is-modulus-uniform-mg (f x) ε (f x') ∘
            is-modulus-uniform-mf x (mg ε) x')

  comp-ucont-function-Metric-Space :
    ucont-function-Metric-Space Y Z →
    ucont-function-Metric-Space X Y →
    ucont-function-Metric-Space X Z
  comp-ucont-function-Metric-Space g f =
    ( map-ucont-function-Metric-Space Y Z g ∘
      map-ucont-function-Metric-Space X Y f) ,
    ( is-ucont-comp-function-Metric-Space
      ( map-ucont-function-Metric-Space Y Z g)
      ( map-ucont-function-Metric-Space X Y f)
      ( is-ucont-map-ucont-function-Metric-Space
        ( Y)
        ( Z)
        ( g))
      ( is-ucont-map-ucont-function-Metric-Space
        ( X)
        ( Y)
        ( f)))
```

### A function is short if and only if the identity is a modulus of uniform continuity for it

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (f : type-function-Metric-Space A B)
  where

  is-short-id-is-modulus-of-uniform-continuity-function-Metric-Space :
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id →
    is-short-function-Metric-Space A B f
  is-short-id-is-modulus-of-uniform-continuity-function-Metric-Space H ε x =
    H x ε

  id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space :
    is-short-function-Metric-Space A B f →
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id
  id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space H x ε =
    H ε x

  is-short-iff-id-is-modulus-of-uniform-continuity-function-Metric-Space :
    is-short-function-Metric-Space A B f ↔
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id
  is-short-iff-id-is-modulus-of-uniform-continuity-function-Metric-Space =
    ( id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space ,
      is-short-id-is-modulus-of-uniform-continuity-function-Metric-Space)
```

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  modulus-of-uniform-continuity-id-Metric-Space :
    modulus-of-uniform-continuity-function-Metric-Space X X id
  modulus-of-uniform-continuity-id-Metric-Space = (id , (λ _ _ _ → id))

  is-ucont-id-Metric-Space :
    is-ucont-function-Metric-Space X X id
  is-ucont-id-Metric-Space =
    unit-trunc-Prop modulus-of-uniform-continuity-id-Metric-Space
```

### Short maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2)
  (B : Metric-Space l3 l4)
  where

  is-ucont-is-short-function-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-short-function-Metric-Space A B f →
    is-ucont-function-Metric-Space A B f
  is-ucont-is-short-function-Metric-Space f H =
    intro-exists id (λ x d → H d x)

  modulated-ucont-short-function-Metric-Space :
    short-function-Metric-Space A B →
    modulated-ucont-function-Metric-Space A B
  modulated-ucont-short-function-Metric-Space (f , H) =
    ( f , id , λ x d → H d x)

  ucont-short-function-Metric-Space :
    short-function-Metric-Space A B →
    ucont-function-Metric-Space A B
  ucont-short-function-Metric-Space =
    tot is-ucont-is-short-function-Metric-Space
```

### Isometries are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  is-ucont-is-isometry-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-isometry-Metric-Space A B f →
    is-ucont-function-Metric-Space A B f
  is-ucont-is-isometry-Metric-Space f =
    is-ucont-is-short-function-Metric-Space A B f ∘
    is-short-is-isometry-Metric-Space A B f

  modulated-ucont-isometry-Metric-Space :
    isometry-Metric-Space A B →
    modulated-ucont-function-Metric-Space A B
  modulated-ucont-isometry-Metric-Space f =
    modulated-ucont-short-function-Metric-Space A B
      ( short-isometry-Metric-Space A B f)

  ucont-isometry-Metric-Space :
    isometry-Metric-Space A B →
    ucont-function-Metric-Space A B
  ucont-isometry-Metric-Space =
    tot is-ucont-is-isometry-Metric-Space
```
