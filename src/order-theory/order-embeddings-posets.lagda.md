# Order embeddings between posets

```agda
module order-theory.order-embeddings-posets where
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
open import foundation.torsorial-type-families
open import foundation.identity-types
open import foundation.sets
open import foundation.homotopies
open import foundation.homotopy-induction

open import order-theory.posets
open import order-theory.order-preserving-maps-posets
open import order-theory.order-reflecting-maps-posets
open import order-theory.order-embeddings-preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be an
{{#concept "order embedding" Disambiguation="poset"}}
if `x ≤ y` in `P` if and only if `f x ≤ f y` in `Q`.  Equivalently, `f`
must be both an [order preserving map](order-theory.order-preserving-maps-posets.md)
and an [order reflecting map](order-theory.order-reflecting-maps-posets.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  where

  is-order-emb-prop-Poset : Prop (l1 ⊔ l2 ⊔ l4)
  is-order-emb-prop-Poset =
    is-order-emb-prop-Preorder (preorder-Poset P) (preorder-Poset Q) f

  is-order-emb-Poset : UU (l1 ⊔ l2 ⊔ l4)
  is-order-emb-Poset = type-Prop is-order-emb-prop-Poset

  is-prop-is-order-emb-Poset : is-prop is-order-emb-Poset
  is-prop-is-order-emb-Poset = is-prop-type-Prop is-order-emb-prop-Poset
```

### The type of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  order-emb-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  order-emb-Poset = order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  map-order-emb-Poset : order-emb-Poset → type-Poset P → type-Poset Q
  map-order-emb-Poset = pr1

  is-order-emb-order-emb-Poset :
    (f : order-emb-Poset) → is-order-emb-Poset P Q (map-order-emb-Poset f)
  is-order-emb-order-emb-Poset = pr2
```

### Homotopies of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-order-emb-Poset : (f g : order-emb-Poset P Q) → UU (l1 ⊔ l3)
  htpy-order-emb-Poset =
    htpy-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  refl-htpy-order-emb-Poset :
    (f : order-emb-Poset P Q) → htpy-order-emb-Poset f f
  refl-htpy-order-emb-Poset f = refl-htpy

  htpy-eq-order-emb-Poset :
    (f g : order-emb-Poset P Q) → f ＝ g → htpy-order-emb-Poset f g
  htpy-eq-order-emb-Poset =
    htpy-eq-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-torsorial-htpy-order-emb-Poset :
    (f : order-emb-Poset P Q) → is-torsorial (htpy-order-emb-Poset f)
  is-torsorial-htpy-order-emb-Poset =
    is-torsorial-htpy-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-equiv-htpy-eq-order-emb-Poset :
    (f g : order-emb-Poset P Q) → is-equiv (htpy-eq-order-emb-Poset f g)
  is-equiv-htpy-eq-order-emb-Poset =
    is-equiv-htpy-eq-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  extensionality-order-emb-Poset :
    (f g : order-emb-Poset P Q) → Id f g ≃ htpy-order-emb-Poset f g
  extensionality-order-emb-Poset =
    extensionality-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)

  eq-htpy-order-emb-Poset :
    (f g : order-emb-Poset P Q) → htpy-order-emb-Poset f g → f ＝ g
  eq-htpy-order-emb-Poset =
    eq-htpy-order-emb-Preorder (preorder-Poset P) (preorder-Poset Q)
```

## Properties

### The identity order embedding

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-order-emb-id-Poset : is-order-emb-Poset P P id
  is-order-emb-id-Poset _ _ = id-iff

  id-order-emb-Poset : order-emb-Poset P P
  id-order-emb-Poset = id , is-order-emb-id-Poset
```

### Composing order embeddings

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  is-order-emb-comp-Poset :
    (g : order-emb-Poset Q R) →
    (f : order-emb-Poset P Q) →
    is-order-emb-Poset P R
      ( map-order-emb-Poset Q R g ∘
        map-order-emb-Poset P Q f)
  is-order-emb-comp-Poset =
    is-order-emb-comp-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)

  comp-order-emb-Poset :
    order-emb-Poset Q R → order-emb-Poset P Q → order-emb-Poset P R
  comp-order-emb-Poset =
    comp-order-emb-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
```

### Unit laws for composition of order embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-order-emb-Poset :
    (f : order-emb-Poset P Q) →
    Id
      ( comp-order-emb-Poset
        ( P)
        ( Q)
        ( Q)
        ( id-order-emb-Poset Q)
        ( f))
      ( f)
  left-unit-law-comp-order-emb-Poset =
    left-unit-law-comp-order-emb-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)

  right-unit-law-comp-order-emb-Poset :
    (f : order-emb-Poset P Q) →
    Id
      ( comp-order-emb-Poset
        ( P)
        ( P)
        ( Q)
        ( f)
        ( id-order-emb-Poset P))
      ( f)
  right-unit-law-comp-order-emb-Poset =
    right-unit-law-comp-order-emb-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
```

### Associativity of composition of order reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : order-emb-Poset R S)
  (g : order-emb-Poset Q R)
  (f : order-emb-Poset P Q)
  where

  associative-comp-order-emb-Poset :
    comp-order-emb-Poset P Q S
      ( comp-order-emb-Poset Q R S h g)
      ( f) ＝
    comp-order-emb-Poset P R S
      ( h)
      ( comp-order-emb-Poset P Q R g f)
  associative-comp-order-emb-Poset =
    associative-comp-order-emb-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
      ( preorder-Poset S)
      ( h)
      ( g)
      ( f)
```

### Order embeddings are order preserving and order reflecting

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  where

  preserves-order-is-order-emb-Poset :
    is-order-emb-Poset P Q f → preserves-order-Poset P Q f
  preserves-order-is-order-emb-Poset H x y = forward-implication (H x y)

  reflects-order-is-order-emb-Poset :
    is-order-emb-Poset P Q f → reflects-order-Poset P Q f
  reflects-order-is-order-emb-Poset H x y = backward-implication (H x y)

  is-order-emb-iff-preserves-reflects-order-Poset :
    (preserves-order-Poset P Q f × reflects-order-Poset P Q f) ↔
    is-order-emb-Poset P Q f
  pr1 is-order-emb-iff-preserves-reflects-order-Poset
    (preserves , reflects) x y = (preserves x y , reflects x y)
  pr1 (pr2 is-order-emb-iff-preserves-reflects-order-Poset is-order-emb) =
    preserves-order-is-order-emb-Poset is-order-emb
  pr2 (pr2 is-order-emb-iff-preserves-reflects-order-Poset is-order-emb) =
    reflects-order-is-order-emb-Poset is-order-emb

module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  hom-order-emb-Poset : order-emb-Poset P Q → hom-Poset P Q
  hom-order-emb-Poset (f , is-order-emb-f) =
    (f , preserves-order-is-order-emb-Poset P Q f is-order-emb-f)

  order-reflecting-map-order-emb-Poset :
    order-emb-Poset P Q → order-reflecting-map-Poset P Q
  order-reflecting-map-order-emb-Poset (f , is-order-emb-f) =
    (f , reflects-order-is-order-emb-Poset P Q f is-order-emb-f)
```

### Order embeddings in posets are embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  inv-eq-order-emb-Poset :
    (f : type-Poset P → type-Poset Q) →
    is-order-emb-Poset P Q f → (x y : type-Poset P) → f x ＝ f y → x ＝ y
  inv-eq-order-emb-Poset f is-order-emb-f x y fx=fy =
    antisymmetric-leq-Poset
      ( P)
      ( x)
      ( y )
      ( backward-implication (is-order-emb-f x y) (leq-eq-Poset Q fx=fy))
      ( backward-implication (is-order-emb-f y x) (leq-eq-Poset Q (inv fx=fy)))

  is-emb-is-order-emb-Poset :
    (f : type-Poset P → type-Poset Q) →
    is-order-emb-Poset P Q f → is-emb f
  pr1 (pr1 (is-emb-is-order-emb-Poset f is-order-emb-f x y)) =
    inv-eq-order-emb-Poset f is-order-emb-f x y
  pr2 (pr1 (is-emb-is-order-emb-Poset f is-order-emb-f x y)) fx=fy =
    is-set-has-uip (is-set-type-Poset Q) (f x) (f y) _ _
  pr1 (pr2 (is-emb-is-order-emb-Poset f is-order-emb-f x y)) =
    inv-eq-order-emb-Poset f is-order-emb-f x y
  pr2 (pr2 (is-emb-is-order-emb-Poset f is-order-emb-f x y)) fx=fy =
    is-set-has-uip (is-set-type-Poset P) x y _ _
```
