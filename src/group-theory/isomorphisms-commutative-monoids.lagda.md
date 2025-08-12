# Isomorphisms of commutative monoids

```agda
module group-theory.isomorphisms-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.equivalences-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.isomorphisms-monoids
```

</details>

## Idea

An
{{#concept "isomorphism" disambiguation="between commutative monoids" Agda=iso-Commutative-Monoid}}
between [commutative monoids](group-theory.commutative-monoids.md) is an
[isomorphism](group-theory.isomorphisms-monoids.md) between their underlying
[monoids](group-theory.monoids.md).

## Definitions

### The predicate of being an isomorphism of commutative monoids

```agda
module _
  {l1 l2 : Level} (A : Commutative-Monoid l1) (B : Commutative-Monoid l2) (f : hom-Commutative-Monoid A B)
  where

  is-iso-Commutative-Monoid : UU (l1 ⊔ l2)
  is-iso-Commutative-Monoid =
    is-iso-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B) f

  is-prop-is-iso-Commutative-Monoid : is-prop is-iso-Commutative-Monoid
  is-prop-is-iso-Commutative-Monoid =
    is-prop-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  is-iso-prop-Commutative-Monoid : Prop (l1 ⊔ l2)
  is-iso-prop-Commutative-Monoid =
    is-iso-prop-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  hom-inv-is-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid → hom-Commutative-Monoid B A
  hom-inv-is-iso-Commutative-Monoid =
    hom-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  map-inv-is-iso-Commutative-Monoid :
    is-iso-Commutative-Monoid → type-Commutative-Monoid B →
    type-Commutative-Monoid A
  map-inv-is-iso-Commutative-Monoid =
    map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  is-section-hom-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid B A B f (hom-inv-is-iso-Commutative-Monoid H) ＝
    id-hom-Commutative-Monoid B
  is-section-hom-inv-is-iso-Commutative-Monoid =
    is-section-hom-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  is-section-map-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    ( map-hom-Commutative-Monoid A B f ∘
      map-hom-Commutative-Monoid B A (hom-inv-is-iso-Commutative-Monoid H)) ~
    id
  is-section-map-inv-is-iso-Commutative-Monoid =
    is-section-map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)

  is-retraction-hom-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid A B A (hom-inv-is-iso-Commutative-Monoid H) f ＝
    id-hom-Commutative-Monoid A
  is-retraction-hom-inv-is-iso-Commutative-Monoid H = pr2 (pr2 H)

  is-retraction-map-inv-is-iso-Commutative-Monoid :
    (H : is-iso-Commutative-Monoid) →
    ( map-inv-is-iso-Commutative-Monoid H ∘ map-hom-Commutative-Monoid A B f) ~
    id
  is-retraction-map-inv-is-iso-Commutative-Monoid =
    is-retraction-map-inv-is-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
      ( f)
```

### The predicate of being an equivalence of commutative monoids

```agda
module _
  {l1 l2 : Level} (A : Commutative-Monoid l1) (B : Commutative-Monoid l2)
  where

  is-equiv-hom-Commutative-Monoid : hom-Commutative-Monoid A B → UU (l1 ⊔ l2)
  is-equiv-hom-Commutative-Monoid =
    is-equiv-hom-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  equiv-Commutative-Monoid : UU (l1 ⊔ l2)
  equiv-Commutative-Monoid =
    equiv-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)
```

### The type of isomorphisms of commutative monoids

```agda
module _
  {l1 l2 : Level} (A : Commutative-Monoid l1) (B : Commutative-Monoid l2)
  where

  iso-Commutative-Monoid : UU (l1 ⊔ l2)
  iso-Commutative-Monoid =
    iso-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)

  hom-iso-Commutative-Monoid :
    iso-Commutative-Monoid → hom-Commutative-Monoid A B
  hom-iso-Commutative-Monoid =
    hom-iso-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)

  map-iso-Commutative-Monoid :
    iso-Commutative-Monoid → type-Commutative-Monoid A →
    type-Commutative-Monoid B
  map-iso-Commutative-Monoid =
    map-iso-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)

  preserves-mul-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) {x y : type-Commutative-Monoid A} →
    map-iso-Commutative-Monoid f (mul-Commutative-Monoid A x y) ＝
    mul-Commutative-Monoid B
      ( map-iso-Commutative-Monoid f x)
      ( map-iso-Commutative-Monoid f y)
  preserves-mul-iso-Commutative-Monoid =
    preserves-mul-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-iso-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    is-iso-Commutative-Monoid A B (hom-iso-Commutative-Monoid f)
  is-iso-iso-Commutative-Monoid =
    is-iso-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  hom-inv-iso-Commutative-Monoid :
    iso-Commutative-Monoid → hom-Commutative-Monoid B A
  hom-inv-iso-Commutative-Monoid =
    hom-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  map-inv-iso-Commutative-Monoid :
    iso-Commutative-Monoid → type-Commutative-Monoid B →
    type-Commutative-Monoid A
  map-inv-iso-Commutative-Monoid =
    map-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  preserves-mul-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) {x y : type-Commutative-Monoid B} →
    map-inv-iso-Commutative-Monoid f (mul-Commutative-Monoid B x y) ＝
    mul-Commutative-Monoid A
      ( map-inv-iso-Commutative-Monoid f x)
      ( map-inv-iso-Commutative-Monoid f y)
  preserves-mul-inv-iso-Commutative-Monoid =
    preserves-mul-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-section-hom-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid B A B
      ( hom-iso-Commutative-Monoid f)
      ( hom-inv-iso-Commutative-Monoid f) ＝
    id-hom-Commutative-Monoid B
  is-section-hom-inv-iso-Commutative-Monoid =
    is-section-hom-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-section-map-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    (map-iso-Commutative-Monoid f ∘ map-inv-iso-Commutative-Monoid f) ~ id
  is-section-map-inv-iso-Commutative-Monoid =
    is-section-map-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-retraction-hom-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    comp-hom-Commutative-Monoid A B A
      ( hom-inv-iso-Commutative-Monoid f)
      ( hom-iso-Commutative-Monoid f) ＝
    id-hom-Commutative-Monoid A
  is-retraction-hom-inv-iso-Commutative-Monoid =
    is-retraction-hom-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-retraction-map-inv-iso-Commutative-Monoid :
    (f : iso-Commutative-Monoid) →
    (map-inv-iso-Commutative-Monoid f ∘ map-iso-Commutative-Monoid f) ~ id
  is-retraction-map-inv-iso-Commutative-Monoid =
    is-retraction-map-inv-iso-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)
```

### The identity isomorphism of commutative monoids

```agda
id-iso-Commutative-Monoid :
  {l : Level} (A : Commutative-Monoid l) → iso-Commutative-Monoid A A
id-iso-Commutative-Monoid A = id-iso-Monoid (monoid-Commutative-Monoid A)
```

## Properties

### Isomorphisms characterize identifications of commutative monoids

```agda
iso-eq-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) → Id A B → iso-Commutative-Monoid A B
iso-eq-Commutative-Monoid A B p =
  iso-eq-Monoid
    ( monoid-Commutative-Monoid A)
    ( monoid-Commutative-Monoid B)
    ( ap pr1 p)

abstract
  equiv-iso-eq-Commutative-Monoid' :
    {l : Level} (A B : Commutative-Monoid l) →
    Id A B ≃ iso-Commutative-Monoid A B
  equiv-iso-eq-Commutative-Monoid' A B =
    ( iso-extensionality-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)) ∘e
    ( equiv-ap-inclusion-subtype is-commutative-prop-Monoid {A} {B})

abstract
  is-torsorial-iso-Commutative-Monoid :
    {l : Level} (A : Commutative-Monoid l) →
    is-torsorial (λ (B : Commutative-Monoid l) → iso-Commutative-Monoid A B)
  is-torsorial-iso-Commutative-Monoid {l} A =
    is-contr-equiv'
      ( Σ (Commutative-Monoid l) (Id A))
      ( equiv-tot (equiv-iso-eq-Commutative-Monoid' A))
      ( is-torsorial-Id A)

is-equiv-iso-eq-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) →
  is-equiv (iso-eq-Commutative-Monoid A B)
is-equiv-iso-eq-Commutative-Monoid A =
  fundamental-theorem-id
    ( is-torsorial-iso-Commutative-Monoid A)
    ( iso-eq-Commutative-Monoid A)

eq-iso-Commutative-Monoid :
  {l : Level} (A B : Commutative-Monoid l) → iso-Commutative-Monoid A B → Id A B
eq-iso-Commutative-Monoid A B =
  map-inv-is-equiv (is-equiv-iso-eq-Commutative-Monoid A B)
```

### A homomorphism of commutative monoids is an isomorphism if and only if its underlying map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : Commutative-Monoid l1) (B : Commutative-Monoid l2)
  where

  is-iso-is-equiv-hom-Commutative-Monoid :
    (f : hom-Commutative-Monoid A B) → is-equiv-hom-Commutative-Monoid A B f →
    is-iso-Commutative-Monoid A B f
  is-iso-is-equiv-hom-Commutative-Monoid =
    is-iso-is-equiv-hom-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  is-equiv-is-iso-Commutative-Monoid :
    (f : hom-Commutative-Monoid A B) → is-iso-Commutative-Monoid A B f →
    is-equiv-hom-Commutative-Monoid A B f
  is-equiv-is-iso-Commutative-Monoid =
    is-equiv-is-iso-hom-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  equiv-iso-equiv-Commutative-Monoid :
    equiv-Commutative-Monoid A B ≃ iso-Commutative-Monoid A B
  equiv-iso-equiv-Commutative-Monoid =
    equiv-iso-equiv-Monoid
      ( monoid-Commutative-Monoid A)
      ( monoid-Commutative-Monoid B)

  iso-equiv-Commutative-Monoid :
    equiv-Commutative-Monoid A B → iso-Commutative-Monoid A B
  iso-equiv-Commutative-Monoid =
    iso-equiv-Monoid (monoid-Commutative-Monoid A) (monoid-Commutative-Monoid B)
```
