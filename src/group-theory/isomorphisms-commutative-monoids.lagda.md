# Isomorphisms of commutative monoids

```agda
module group-theory.isomorphisms-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.invertible-elements-commutative-monoids
open import group-theory.isomorphisms-monoids
open import group-theory.precategory-of-commutative-monoids
```

</details>

## Idea

An **isomorphism** of [monoids](group-theory.monoids.md) is an invertible
[homomorphism of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  (f : hom-Commutative-Monoid M N)
  where

  is-iso-Commutative-Monoid : UU (l1 ⊔ l2)
  is-iso-Commutative-Monoid =
    is-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N} f

  map-inv-is-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid → type-Commutative-Monoid N →
    type-Commutative-Monoid M
  map-inv-is-iso-Commutative-Monoid =
    map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  hom-inv-is-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid → hom-Commutative-Monoid N M
  hom-inv-is-iso-Commutative-Monoid =
    hom-inv-is-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-section-hom-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid N M N f (hom-inv-is-iso-Commutative-Monoid H) ＝
    id-hom-Commutative-Monoid N
  is-section-hom-inv-is-iso-Commutative-Monoid =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-section-map-inv-is-iso-Commutative-Monoid :
    ( U : is-iso-Commutative-Monoid) →
    ( map-hom-Commutative-Monoid M N f ∘ map-inv-is-iso-Commutative-Monoid U) ~
    id
  is-section-map-inv-is-iso-Commutative-Monoid =
    is-section-map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  is-retraction-hom-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid M N M (hom-inv-is-iso-Commutative-Monoid H) f ＝
    id-hom-Commutative-Monoid M
  is-retraction-hom-inv-is-iso-Commutative-Monoid =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-retraction-map-inv-is-iso-Commutative-Monoid :
    ( U : is-iso-Commutative-Monoid) →
    ( map-inv-is-iso-Commutative-Monoid U ∘ map-hom-Commutative-Monoid M N f) ~
    id
  is-retraction-map-inv-is-iso-Commutative-Monoid =
    is-retraction-map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)
```

### Isomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  iso-Commutative-Monoid : UU (l1 ⊔ l2)
  iso-Commutative-Monoid =
    iso-Large-Precategory Commutative-Monoid-Large-Precategory M N

  hom-iso-Commutative-Monoid :
    iso-Commutative-Monoid → hom-Commutative-Monoid M N
  hom-iso-Commutative-Monoid =
    hom-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}

  map-iso-Commutative-Monoid :
    iso-Commutative-Monoid → type-Commutative-Monoid M → type-Commutative-Monoid N
  map-iso-Commutative-Monoid f =
    map-hom-Commutative-Monoid M N (hom-iso-Commutative-Monoid f)

  preserves-mul-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) {x y : type-Commutative-Monoid M} →
    map-iso-Commutative-Monoid f (mul-Commutative-Monoid M x y) ＝
    mul-Commutative-Monoid N (map-iso-Commutative-Monoid f x) (map-iso-Commutative-Monoid f y)
  preserves-mul-iso-Commutative-Monoid f =
    preserves-mul-hom-Commutative-Monoid M N (hom-iso-Commutative-Monoid f)

  is-iso-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    is-iso-Commutative-Monoid M N (hom-iso-Commutative-Monoid f)
  is-iso-iso-Commutative-Monoid =
    is-iso-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}

  hom-inv-iso-Commutative-Monoid :
    iso-Commutative-Monoid → hom-Commutative-Monoid N M
  hom-inv-iso-Commutative-Monoid =
    hom-inv-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}

  map-inv-iso-Commutative-Monoid :
    iso-Commutative-Monoid → type-Commutative-Monoid N → type-Commutative-Monoid M
  map-inv-iso-Commutative-Monoid f =
    map-hom-Commutative-Monoid N M (hom-inv-iso-Commutative-Monoid f)

  preserves-mul-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) {x y : type-Commutative-Monoid N} →
    map-inv-iso-Commutative-Monoid f (mul-Commutative-Monoid N x y) ＝
    mul-Commutative-Monoid M (map-inv-iso-Commutative-Monoid f x) (map-inv-iso-Commutative-Monoid f y)
  preserves-mul-inv-iso-Commutative-Monoid f =
    preserves-mul-hom-Commutative-Monoid N M (hom-inv-iso-Commutative-Monoid f)

  is-section-hom-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid N M N (hom-iso-Commutative-Monoid f) (hom-inv-iso-Commutative-Monoid f) ＝
    id-hom-Commutative-Monoid N
  is-section-hom-inv-iso-Commutative-Monoid =
    is-section-hom-inv-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-section-map-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    map-iso-Commutative-Monoid f ∘ map-inv-iso-Commutative-Monoid f ~ id
  is-section-map-inv-iso-Commutative-Monoid f =
    htpy-eq-hom-Commutative-Monoid N N
      ( comp-hom-Commutative-Monoid N M N (hom-iso-Commutative-Monoid f) (hom-inv-iso-Commutative-Monoid f))
      ( id-hom-Commutative-Monoid N)
      ( is-section-hom-inv-iso-Commutative-Monoid f)

  is-retraction-hom-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid M N M (hom-inv-iso-Commutative-Monoid f) (hom-iso-Commutative-Monoid f) ＝
    id-hom-Commutative-Monoid M
  is-retraction-hom-inv-iso-Commutative-Monoid =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-retraction-map-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    map-inv-iso-Commutative-Monoid f ∘ map-iso-Commutative-Monoid f ~ id
  is-retraction-map-inv-iso-Commutative-Monoid f =
    htpy-eq-hom-Commutative-Monoid M M
      ( comp-hom-Commutative-Monoid M N M (hom-inv-iso-Commutative-Monoid f) (hom-iso-Commutative-Monoid f))
      ( id-hom-Commutative-Monoid M)
      ( is-retraction-hom-inv-iso-Commutative-Monoid f)
```

## Examples

### Identity homomorphisms are isomorphisms

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-iso-id-hom-Commutative-Monoid :
    is-iso-Commutative-Monoid M M (id-hom-Commutative-Monoid M)
  is-iso-id-hom-Commutative-Monoid =
    is-iso-id-hom-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}

  id-iso-Commutative-Monoid : iso-Commutative-Monoid M M
  id-iso-Commutative-Monoid =
    id-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are propositions
(since the hom-types are sets). But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'`.

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  is-prop-is-iso-Commutative-Monoid :
    (f : hom-Commutative-Monoid M N) →
    is-prop (is-iso-Commutative-Monoid M N f)
  is-prop-is-iso-Commutative-Monoid =
    is-prop-is-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
  is-iso-prop-Commutative-Monoid :
    (f : hom-Commutative-Monoid M N) → Prop (l1 ⊔ l2)
  is-iso-prop-Commutative-Monoid =
    is-iso-prop-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  is-set-iso-Commutative-Monoid : is-set (iso-Commutative-Monoid M N)
  is-set-iso-Commutative-Monoid =
    is-set-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}

  iso-set-Commutative-Monoid : Set (l1 ⊔ l2)
  iso-set-Commutative-Monoid =
    iso-set-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N}
```

### Isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2) (K : Commutative-Monoid l3)
  (g : iso-Commutative-Monoid N K) (f : iso-Commutative-Monoid M N)
  where

  hom-comp-iso-Commutative-Monoid : hom-Commutative-Monoid M K
  hom-comp-iso-Commutative-Monoid =
    hom-comp-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  is-iso-comp-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid M K hom-comp-iso-Commutative-Monoid
  is-iso-comp-iso-Commutative-Monoid =
    is-iso-comp-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  comp-iso-Commutative-Monoid : iso-Commutative-Monoid M K
  comp-iso-Commutative-Monoid =
    comp-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2) (f : iso-Commutative-Monoid M N)
  where

  is-iso-inv-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid N M (hom-inv-iso-Commutative-Monoid M N f)
  is-iso-inv-iso-Commutative-Monoid =
    is-iso-inv-is-iso-Large-Precategory
      ( Commutative-Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( is-iso-iso-Commutative-Monoid M N f)

  inv-iso-Commutative-Monoid : iso-Commutative-Monoid N M
  inv-iso-Commutative-Monoid =
    inv-iso-Large-Precategory Commutative-Monoid-Large-Precategory {X = M} {Y = N} f
```

### Any isomorphism of monoids preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  (f : iso-Commutative-Monoid M N)
  where

  preserves-invertible-elements-iso-Commutative-Monoid :
    {x : type-Commutative-Monoid M} →
    is-invertible-element-Commutative-Monoid M x →
    is-invertible-element-Commutative-Monoid N
      ( map-iso-Commutative-Monoid M N f x)
  preserves-invertible-elements-iso-Commutative-Monoid =
    preserves-invertible-elements-hom-Commutative-Monoid M N
      ( hom-iso-Commutative-Monoid M N f)

  reflects-invertible-elements-iso-Commutative-Monoid :
    {x : type-Commutative-Monoid M} →
    is-invertible-element-Commutative-Monoid N
      ( map-iso-Commutative-Monoid M N f x) →
    is-invertible-element-Commutative-Monoid M x
  reflects-invertible-elements-iso-Commutative-Monoid H =
    tr
      ( is-invertible-element-Commutative-Monoid M)
      ( is-retraction-map-inv-iso-Commutative-Monoid M N f _)
      ( preserves-invertible-elements-hom-Commutative-Monoid N M
        ( hom-inv-iso-Commutative-Monoid M N f)
        ( H))
```

### Isomorphisms characterize identifications of commutative monoids

```agda
iso-eq-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) → Id A B → iso-Commutative-Monoid A B
iso-eq-Commutative-Monoid A B p =
  iso-eq-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B) (ap pr1 p)

abstract
  equiv-iso-eq-Commutative-Monoid' :
    {l : Level} (A B : Commutative-Monoid l) → Id A B ≃ iso-Commutative-Monoid A B
  equiv-iso-eq-Commutative-Monoid' A B =
    ( extensionality-Monoid' (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)) ∘e
    ( equiv-ap-inclusion-subtype is-abelian-prop-Monoid {A} {B})

abstract
  is-torsorial-iso-Commutative-Monoid :
    {l : Level} (A : Commutative-Monoid l) → is-torsorial (λ (B : Commutative-Monoid l) → iso-Commutative-Monoid A B)
  is-torsorial-iso-Commutative-Monoid {l} A =
    is-contr-equiv'
      ( Σ (Commutative-Monoid l) (Id A))
      ( equiv-tot (equiv-iso-eq-Commutative-Monoid' A))
      ( is-torsorial-Id A)

is-equiv-iso-eq-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) → is-equiv (iso-eq-Commutative-Monoid A B)
is-equiv-iso-eq-Commutative-Monoid A =
  fundamental-theorem-id
    ( is-torsorial-iso-Commutative-Monoid A)
    ( iso-eq-Commutative-Monoid A)

eq-iso-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) → iso-Commutative-Monoid A B → Id A B
eq-iso-Commutative-Monoid A B =
  map-inv-is-equiv (is-equiv-iso-eq-Commutative-Monoid A B)
```
