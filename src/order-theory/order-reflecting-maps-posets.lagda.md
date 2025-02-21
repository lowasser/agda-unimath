# Order reflecting maps between posets

```agda
module order-theory.order-reflecting-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.order-reflecting-maps-preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be an
{{#concept "order reflecting map" Disambiguation="poset" Agda=order-reflecting-map-Poset}}
if whenever `f x ≤ f y` in `Q`, `x ≤ y` in `P`.

## Definition

### The predicate of being an order reflecting map

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  where

  reflects-order-prop-Poset : Prop (l1 ⊔ l2 ⊔ l4)
  reflects-order-prop-Poset =
    reflects-order-prop-Preorder (preorder-Poset P) (preorder-Poset Q) f

  reflects-order-Poset : UU (l1 ⊔ l2 ⊔ l4)
  reflects-order-Poset = type-Prop reflects-order-prop-Poset

  is-prop-reflects-order-Poset : is-prop reflects-order-Poset
  is-prop-reflects-order-Poset =
    is-prop-type-Prop reflects-order-prop-Poset
```

### The type of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  order-reflecting-map-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  order-reflecting-map-Poset =
    order-reflecting-map-Preorder (preorder-Poset P) (preorder-Poset Q)

  map-order-reflecting-map-Poset :
    order-reflecting-map-Poset → type-Poset P → type-Poset Q
  map-order-reflecting-map-Poset = pr1

  reflects-order-order-reflecting-map-Poset :
    (f : order-reflecting-map-Poset) →
    reflects-order-Poset P Q (map-order-reflecting-map-Poset f)
  reflects-order-order-reflecting-map-Poset = pr2
```

### Homotopies of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-order-reflecting-map-Poset :
    (f g : order-reflecting-map-Poset P Q) → UU (l1 ⊔ l3)
  htpy-order-reflecting-map-Poset f g =
    htpy-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( f)
      ( g)

  refl-htpy-order-reflecting-map-Poset :
    (f : order-reflecting-map-Poset P Q) →
    htpy-order-reflecting-map-Poset f f
  refl-htpy-order-reflecting-map-Poset f = refl-htpy

  htpy-eq-order-reflecting-map-Poset :
    (f g : order-reflecting-map-Poset P Q) → f ＝ g →
    htpy-order-reflecting-map-Poset f g
  htpy-eq-order-reflecting-map-Poset =
    htpy-eq-order-reflecting-map-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-torsorial-htpy-order-reflecting-map-Poset :
    (f : order-reflecting-map-Poset P Q) →
    is-torsorial (htpy-order-reflecting-map-Poset f)
  is-torsorial-htpy-order-reflecting-map-Poset =
    is-torsorial-htpy-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)

  is-equiv-htpy-eq-order-reflecting-map-Poset :
    (f g : order-reflecting-map-Poset P Q) →
    is-equiv (htpy-eq-order-reflecting-map-Poset f g)
  is-equiv-htpy-eq-order-reflecting-map-Poset f g =
    is-equiv-htpy-eq-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( f)
      ( g)

  extensionality-order-reflecting-map-Poset :
    (f g : order-reflecting-map-Poset P Q) →
    Id f g ≃ htpy-order-reflecting-map-Poset f g
  extensionality-order-reflecting-map-Poset =
    extensionality-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)

  eq-htpy-order-reflecting-map-Poset :
    (f g : order-reflecting-map-Poset P Q) →
    htpy-order-reflecting-map-Poset f g →
    f ＝ g
  eq-htpy-order-reflecting-map-Poset =
    eq-htpy-order-reflecting-map-Preorder (preorder-Poset P) (preorder-Poset Q)
```

### The identity order reflecting map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  reflects-order-id-Poset : reflects-order-Poset P P id
  reflects-order-id-Poset _ _ x≤y = x≤y

  id-order-reflecting-map-Poset : order-reflecting-map-Poset P P
  id-order-reflecting-map-Poset = id , reflects-order-id-Poset
```

### Composing order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  reflects-order-comp-Poset :
    (g : order-reflecting-map-Poset Q R) →
    (f : order-reflecting-map-Poset P Q) →
    reflects-order-Poset P R
      ( map-order-reflecting-map-Poset Q R g ∘
        map-order-reflecting-map-Poset P Q f)
  reflects-order-comp-Poset =
    reflects-order-comp-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)

  comp-order-reflecting-map-Poset :
    order-reflecting-map-Poset Q R → order-reflecting-map-Poset P Q →
    order-reflecting-map-Poset P R
  comp-order-reflecting-map-Poset =
    comp-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
```

### Unit laws for composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-order-reflecting-map-Poset :
    (f : order-reflecting-map-Poset P Q) →
    Id
      ( comp-order-reflecting-map-Poset
        ( P)
        ( Q)
        ( Q)
        ( id-order-reflecting-map-Poset Q)
        ( f))
      ( f)
  left-unit-law-comp-order-reflecting-map-Poset =
    left-unit-law-comp-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)

  right-unit-law-comp-order-reflecting-map-Poset :
    (f : order-reflecting-map-Poset P Q) →
    Id
      ( comp-order-reflecting-map-Poset
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-reflecting-map-Poset P))
      ( f)
  right-unit-law-comp-order-reflecting-map-Poset =
    right-unit-law-comp-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
```

### Associativity of composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : order-reflecting-map-Poset R S)
  (g : order-reflecting-map-Poset Q R)
  (f : order-reflecting-map-Poset P Q)
  where

  associative-comp-order-reflecting-map-Poset :
    comp-order-reflecting-map-Poset P Q S
      ( comp-order-reflecting-map-Poset Q R S h g)
      ( f) ＝
    comp-order-reflecting-map-Poset P R S
      ( h)
      ( comp-order-reflecting-map-Poset P Q R g f)
  associative-comp-order-reflecting-map-Poset =
    associative-comp-order-reflecting-map-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
      ( preorder-Poset S)
      ( h)
      ( g)
      ( f)
```
