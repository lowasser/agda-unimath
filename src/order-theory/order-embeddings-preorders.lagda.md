# Order embeddings between preorders

```agda
module order-theory.order-embeddings-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.universe-levels
open import foundation.embeddings
open import foundation.propositions
open import foundation.function-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.homotopies
open import foundation.homotopy-induction

open import order-theory.preorders
open import order-theory.order-preserving-maps-preorders
open import order-theory.order-reflecting-maps-preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[preorders](order-theory.preorders.md) is said to be an
{{#concept "order embedding" Disambiguation="preorder"}}
if `x ≤ y` in `P` if and only if `f x ≤ f y` in `Q`.  Equivalently, `f`
must be both an [order preserving map](order-theory.order-preserving-maps-preorders.md)
and an [order reflecting map](order-theory.order-reflecting-maps-preorders.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (f : type-Preorder P → type-Preorder Q)
  where

  is-order-emb-prop-Preorder : Prop (l1 ⊔ l2 ⊔ l4)
  is-order-emb-prop-Preorder =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( type-Preorder P)
          ( λ y →
            leq-prop-Preorder P x y ⇔
            leq-prop-Preorder Q (f x) (f y)))

  is-order-emb-Preorder : UU (l1 ⊔ l2 ⊔ l4)
  is-order-emb-Preorder = type-Prop is-order-emb-prop-Preorder

  is-prop-is-order-emb-Preorder : is-prop is-order-emb-Preorder
  is-prop-is-order-emb-Preorder = is-prop-type-Prop is-order-emb-prop-Preorder
```

### The type of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  order-emb-Preorder : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  order-emb-Preorder =
    Σ (type-Preorder P → type-Preorder Q) (is-order-emb-Preorder P Q)

  map-order-emb-Preorder :
    order-emb-Preorder → type-Preorder P → type-Preorder Q
  map-order-emb-Preorder = pr1

  is-order-emb-order-emb-Preorder :
    (f : order-emb-Preorder) →
    is-order-emb-Preorder P Q (map-order-emb-Preorder f)
  is-order-emb-order-emb-Preorder = pr2
```

### Homotopies of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  htpy-order-emb-Preorder :
    (f g : order-emb-Preorder P Q) → UU (l1 ⊔ l3)
  htpy-order-emb-Preorder f g =
    map-order-emb-Preorder P Q f ~
    map-order-emb-Preorder P Q g

  refl-htpy-order-emb-Preorder :
    (f : order-emb-Preorder P Q) →
    htpy-order-emb-Preorder f f
  refl-htpy-order-emb-Preorder f = refl-htpy

  htpy-eq-order-emb-Preorder :
    (f g : order-emb-Preorder P Q) → f ＝ g →
    htpy-order-emb-Preorder f g
  htpy-eq-order-emb-Preorder f .f refl =
    refl-htpy-order-emb-Preorder f

  is-torsorial-htpy-order-emb-Preorder :
    (f : order-emb-Preorder P Q) →
    is-torsorial (htpy-order-emb-Preorder f)
  is-torsorial-htpy-order-emb-Preorder f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-order-emb-Preorder P Q f))
      ( is-prop-is-order-emb-Preorder P Q)
      ( map-order-emb-Preorder P Q f)
      ( refl-htpy)
      ( is-order-emb-order-emb-Preorder P Q f)

  is-equiv-htpy-eq-order-emb-Preorder :
    (f g : order-emb-Preorder P Q) →
    is-equiv (htpy-eq-order-emb-Preorder f g)
  is-equiv-htpy-eq-order-emb-Preorder f =
    fundamental-theorem-id
      ( is-torsorial-htpy-order-emb-Preorder f)
      ( htpy-eq-order-emb-Preorder f)

  extensionality-order-emb-Preorder :
    (f g : order-emb-Preorder P Q) →
    Id f g ≃ htpy-order-emb-Preorder f g
  pr1 (extensionality-order-emb-Preorder f g) =
    htpy-eq-order-emb-Preorder f g
  pr2 (extensionality-order-emb-Preorder f g) =
    is-equiv-htpy-eq-order-emb-Preorder f g

  eq-htpy-order-emb-Preorder :
    (f g : order-emb-Preorder P Q) →
    htpy-order-emb-Preorder f g →
    f ＝ g
  eq-htpy-order-emb-Preorder f g =
    map-inv-is-equiv (is-equiv-htpy-eq-order-emb-Preorder f g)
```

## Properties

### The identity order embedding

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-order-emb-id-Preorder : is-order-emb-Preorder P P id
  is-order-emb-id-Preorder _ _ = id-iff

  id-order-emb-Preorder : order-emb-Preorder P P
  id-order-emb-Preorder = id , is-order-emb-id-Preorder
```

### Composing order embeddings

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4) (R : Preorder l5 l6)
  where

  is-order-emb-comp-Preorder :
    (g : order-emb-Preorder Q R) →
    (f : order-emb-Preorder P Q) →
    is-order-emb-Preorder P R
      ( map-order-emb-Preorder Q R g ∘
        map-order-emb-Preorder P Q f)
  is-order-emb-comp-Preorder g f x y =
    logical-equivalence-reasoning
      leq-Preorder P x y
      ↔ leq-Preorder
        ( Q)
        ( map-order-emb-Preorder P Q f x)
        ( map-order-emb-Preorder P Q f y)
        by is-order-emb-order-emb-Preorder P Q f x y
      ↔ leq-Preorder
        ( R)
        ( map-order-emb-Preorder Q R g (map-order-emb-Preorder P Q f x))
        ( map-order-emb-Preorder Q R g (map-order-emb-Preorder P Q f y))
        by is-order-emb-order-emb-Preorder Q R g _ _

  comp-order-emb-Preorder :
    order-emb-Preorder Q R → order-emb-Preorder P Q →
    order-emb-Preorder P R
  pr1 (comp-order-emb-Preorder g f) =
    map-order-emb-Preorder Q R g ∘
    map-order-emb-Preorder P Q f
  pr2 (comp-order-emb-Preorder g f) =
    is-order-emb-comp-Preorder g f
```

### Unit laws for composition of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  left-unit-law-comp-order-emb-Preorder :
    (f : order-emb-Preorder P Q) →
    Id
      ( comp-order-emb-Preorder
        ( P)
        ( Q)
        ( Q)
        ( id-order-emb-Preorder Q)
        ( f))
      ( f)
  left-unit-law-comp-order-emb-Preorder f =
    eq-htpy-order-emb-Preorder
      ( P)
      ( Q)
      ( comp-order-emb-Preorder
        ( P)
        ( Q)
        ( Q)
        ( id-order-emb-Preorder Q)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-order-emb-Preorder :
    (f : order-emb-Preorder P Q) →
    Id
      ( comp-order-emb-Preorder
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-emb-Preorder P))
      ( f)
  right-unit-law-comp-order-emb-Preorder f =
    eq-htpy-order-emb-Preorder
      ( P)
      ( Q)
      ( comp-order-emb-Preorder
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-emb-Preorder P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (R : Preorder l5 l6) (S : Preorder l7 l8)
  (h : order-emb-Preorder R S)
  (g : order-emb-Preorder Q R)
  (f : order-emb-Preorder P Q)
  where

  associative-comp-order-emb-Preorder :
    comp-order-emb-Preorder P Q S
      ( comp-order-emb-Preorder Q R S h g)
      ( f) ＝
    comp-order-emb-Preorder P R S
      ( h)
      ( comp-order-emb-Preorder P Q R g f)
  associative-comp-order-emb-Preorder =
    eq-htpy-order-emb-Preorder P S
      ( comp-order-emb-Preorder P Q S
        ( comp-order-emb-Preorder Q R S h g)
        ( f))
      ( comp-order-emb-Preorder P R S
        ( h)
        ( comp-order-emb-Preorder P Q R g f))
      ( refl-htpy)
```

### Order embeddings are order preserving and order reflecting

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (f : type-Preorder P → type-Preorder Q)
  where

  preserves-order-is-order-emb-Preorder :
    is-order-emb-Preorder P Q f → preserves-order-Preorder P Q f
  preserves-order-is-order-emb-Preorder H x y = forward-implication (H x y)

  reflects-order-is-order-emb-Preorder :
    is-order-emb-Preorder P Q f → reflects-order-Preorder P Q f
  reflects-order-is-order-emb-Preorder H x y = backward-implication (H x y)

  is-order-emb-iff-preserves-reflects-order-Preorder :
    (preserves-order-Preorder P Q f × reflects-order-Preorder P Q f) ↔
    is-order-emb-Preorder P Q f
  pr1 is-order-emb-iff-preserves-reflects-order-Preorder
    (preserves , reflects) x y = (preserves x y , reflects x y)
  pr1 (pr2 is-order-emb-iff-preserves-reflects-order-Preorder is-emb) =
    preserves-order-is-order-emb-Preorder is-emb
  pr2 (pr2 is-order-emb-iff-preserves-reflects-order-Preorder is-emb) =
    reflects-order-is-order-emb-Preorder is-emb
```
