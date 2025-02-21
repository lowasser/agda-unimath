# Order reflecting maps between preorders

```agda
module order-theory.order-reflecting-maps-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[preorders](order-theory.preorders.md) is said to be an
{{#concept "order reflecting map" Disambiguation="preorder" Agda=order-reflecting-map-Preorder}}
if whenever `f x ≤ f y` in `Q`, `x ≤ y` in `P`.

## Definition

### The predicate of being an order reflecting map

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (f : type-Preorder P → type-Preorder Q)
  where

  reflects-order-prop-Preorder : Prop (l1 ⊔ l2 ⊔ l4)
  reflects-order-prop-Preorder =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( type-Preorder P)
          ( λ y →
            hom-Prop
              ( leq-prop-Preorder Q (f x) (f y))
              ( leq-prop-Preorder P x y)))

  reflects-order-Preorder : UU (l1 ⊔ l2 ⊔ l4)
  reflects-order-Preorder = type-Prop reflects-order-prop-Preorder

  is-prop-reflects-order-Preorder : is-prop reflects-order-Preorder
  is-prop-reflects-order-Preorder =
    is-prop-type-Prop reflects-order-prop-Preorder
```

### The type of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  order-reflecting-map-Preorder : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  order-reflecting-map-Preorder =
    Σ (type-Preorder P → type-Preorder Q) (reflects-order-Preorder P Q)

  map-order-reflecting-map-Preorder :
    order-reflecting-map-Preorder → type-Preorder P → type-Preorder Q
  map-order-reflecting-map-Preorder = pr1

  reflects-order-order-reflecting-map-Preorder :
    (f : order-reflecting-map-Preorder) →
    reflects-order-Preorder P Q (map-order-reflecting-map-Preorder f)
  reflects-order-order-reflecting-map-Preorder = pr2
```

### Homotopies of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  htpy-order-reflecting-map-Preorder :
    (f g : order-reflecting-map-Preorder P Q) → UU (l1 ⊔ l3)
  htpy-order-reflecting-map-Preorder f g =
    map-order-reflecting-map-Preorder P Q f ~
    map-order-reflecting-map-Preorder P Q g

  refl-htpy-order-reflecting-map-Preorder :
    (f : order-reflecting-map-Preorder P Q) →
    htpy-order-reflecting-map-Preorder f f
  refl-htpy-order-reflecting-map-Preorder f = refl-htpy

  htpy-eq-order-reflecting-map-Preorder :
    (f g : order-reflecting-map-Preorder P Q) → f ＝ g →
    htpy-order-reflecting-map-Preorder f g
  htpy-eq-order-reflecting-map-Preorder f .f refl =
    refl-htpy-order-reflecting-map-Preorder f

  is-torsorial-htpy-order-reflecting-map-Preorder :
    (f : order-reflecting-map-Preorder P Q) →
    is-torsorial (htpy-order-reflecting-map-Preorder f)
  is-torsorial-htpy-order-reflecting-map-Preorder f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-order-reflecting-map-Preorder P Q f))
      ( is-prop-reflects-order-Preorder P Q)
      ( map-order-reflecting-map-Preorder P Q f)
      ( refl-htpy)
      ( reflects-order-order-reflecting-map-Preorder P Q f)

  is-equiv-htpy-eq-order-reflecting-map-Preorder :
    (f g : order-reflecting-map-Preorder P Q) →
    is-equiv (htpy-eq-order-reflecting-map-Preorder f g)
  is-equiv-htpy-eq-order-reflecting-map-Preorder f =
    fundamental-theorem-id
      ( is-torsorial-htpy-order-reflecting-map-Preorder f)
      ( htpy-eq-order-reflecting-map-Preorder f)

  extensionality-order-reflecting-map-Preorder :
    (f g : order-reflecting-map-Preorder P Q) →
    Id f g ≃ htpy-order-reflecting-map-Preorder f g
  pr1 (extensionality-order-reflecting-map-Preorder f g) =
    htpy-eq-order-reflecting-map-Preorder f g
  pr2 (extensionality-order-reflecting-map-Preorder f g) =
    is-equiv-htpy-eq-order-reflecting-map-Preorder f g

  eq-htpy-order-reflecting-map-Preorder :
    (f g : order-reflecting-map-Preorder P Q) →
    htpy-order-reflecting-map-Preorder f g →
    f ＝ g
  eq-htpy-order-reflecting-map-Preorder f g =
    map-inv-is-equiv (is-equiv-htpy-eq-order-reflecting-map-Preorder f g)
```

### The identity order reflecting map

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  reflects-order-id-Preorder : reflects-order-Preorder P P id
  reflects-order-id-Preorder _ _ x≤y = x≤y

  id-order-reflecting-map-Preorder : order-reflecting-map-Preorder P P
  id-order-reflecting-map-Preorder = id , reflects-order-id-Preorder
```

### Composing order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4) (R : Preorder l5 l6)
  where

  reflects-order-comp-Preorder :
    (g : order-reflecting-map-Preorder Q R) →
    (f : order-reflecting-map-Preorder P Q) →
    reflects-order-Preorder P R
      ( map-order-reflecting-map-Preorder Q R g ∘
        map-order-reflecting-map-Preorder P Q f)
  reflects-order-comp-Preorder g f x y gfx≤gfy =
    reflects-order-order-reflecting-map-Preorder
      ( P)
      ( Q)
      ( f)
      ( x)
      ( y)
      ( reflects-order-order-reflecting-map-Preorder
        ( Q)
        ( R)
        ( g)
        ( map-order-reflecting-map-Preorder P Q f x)
        ( map-order-reflecting-map-Preorder P Q f y)
        ( gfx≤gfy))

  comp-order-reflecting-map-Preorder :
    order-reflecting-map-Preorder Q R → order-reflecting-map-Preorder P Q →
    order-reflecting-map-Preorder P R
  pr1 (comp-order-reflecting-map-Preorder g f) =
    map-order-reflecting-map-Preorder Q R g ∘
    map-order-reflecting-map-Preorder P Q f
  pr2 (comp-order-reflecting-map-Preorder g f) =
    reflects-order-comp-Preorder g f
```

### Unit laws for composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  left-unit-law-comp-order-reflecting-map-Preorder :
    (f : order-reflecting-map-Preorder P Q) →
    Id
      ( comp-order-reflecting-map-Preorder
        ( P)
        ( Q)
        ( Q)
        ( id-order-reflecting-map-Preorder Q)
        ( f))
      ( f)
  left-unit-law-comp-order-reflecting-map-Preorder f =
    eq-htpy-order-reflecting-map-Preorder
      ( P)
      ( Q)
      ( comp-order-reflecting-map-Preorder
        ( P)
        ( Q)
        ( Q)
        ( id-order-reflecting-map-Preorder Q)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-order-reflecting-map-Preorder :
    (f : order-reflecting-map-Preorder P Q) →
    Id
      ( comp-order-reflecting-map-Preorder
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-reflecting-map-Preorder P))
      ( f)
  right-unit-law-comp-order-reflecting-map-Preorder f =
    eq-htpy-order-reflecting-map-Preorder
      ( P)
      ( Q)
      ( comp-order-reflecting-map-Preorder
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-reflecting-map-Preorder P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (R : Preorder l5 l6) (S : Preorder l7 l8)
  (h : order-reflecting-map-Preorder R S)
  (g : order-reflecting-map-Preorder Q R)
  (f : order-reflecting-map-Preorder P Q)
  where

  associative-comp-order-reflecting-map-Preorder :
    comp-order-reflecting-map-Preorder P Q S
      ( comp-order-reflecting-map-Preorder Q R S h g)
      ( f) ＝
    comp-order-reflecting-map-Preorder P R S
      ( h)
      ( comp-order-reflecting-map-Preorder P Q R g f)
  associative-comp-order-reflecting-map-Preorder =
    eq-htpy-order-reflecting-map-Preorder P S
      ( comp-order-reflecting-map-Preorder P Q S
        ( comp-order-reflecting-map-Preorder Q R S h g)
        ( f))
      ( comp-order-reflecting-map-Preorder P R S
        ( h)
        ( comp-order-reflecting-map-Preorder P Q R g f))
      ( refl-htpy)
```
