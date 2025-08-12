# Isomorphisms of monoids

```agda
module group-theory.isomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.equivalences-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.precategory-of-monoids
```

</details>

## Idea

An **isomorphism** of [monoids](group-theory.monoids.md) is an invertible
[homomorphism of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  is-iso-Monoid : UU (l1 ⊔ l2)
  is-iso-Monoid =
    is-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f

  hom-inv-is-iso-Monoid : is-iso-Monoid → hom-Monoid N M
  hom-inv-is-iso-Monoid =
    hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  map-inv-is-iso-Monoid : is-iso-Monoid → type-Monoid N → type-Monoid M
  map-inv-is-iso-Monoid H = map-hom-Monoid N M (hom-inv-is-iso-Monoid H)

  is-section-hom-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    comp-hom-Monoid N M N f (hom-inv-is-iso-Monoid H) ＝
    id-hom-Monoid N
  is-section-hom-inv-is-iso-Monoid =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-section-map-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    map-hom-Monoid M N f ∘ map-inv-is-iso-Monoid H ~ id
  is-section-map-inv-is-iso-Monoid H n =
    ap (λ h → map-hom-Monoid N N h n) (is-section-hom-inv-is-iso-Monoid H)

  is-retraction-hom-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    comp-hom-Monoid M N M (hom-inv-is-iso-Monoid H) f ＝
    id-hom-Monoid M
  is-retraction-hom-inv-is-iso-Monoid =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-retraction-map-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    map-inv-is-iso-Monoid H ∘ map-hom-Monoid M N f ~ id
  is-retraction-map-inv-is-iso-Monoid H m =
    ap (λ h → map-hom-Monoid M M h m) (is-retraction-hom-inv-is-iso-Monoid H)
```

### Isomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  iso-Monoid : UU (l1 ⊔ l2)
  iso-Monoid =
    iso-Large-Precategory Monoid-Large-Precategory M N

  hom-iso-Monoid :
    iso-Monoid → hom-Monoid M N
  hom-iso-Monoid =
    hom-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  map-iso-Monoid :
    iso-Monoid → type-Monoid M → type-Monoid N
  map-iso-Monoid f = map-hom-Monoid M N (hom-iso-Monoid f)

  preserves-mul-iso-Monoid :
    (f : iso-Monoid) {x y : type-Monoid M} →
    map-iso-Monoid f (mul-Monoid M x y) ＝
    mul-Monoid N (map-iso-Monoid f x) (map-iso-Monoid f y)
  preserves-mul-iso-Monoid f =
    preserves-mul-hom-Monoid M N (hom-iso-Monoid f)

  is-iso-iso-Monoid :
    (f : iso-Monoid) →
    is-iso-Monoid M N (hom-iso-Monoid f)
  is-iso-iso-Monoid =
    is-iso-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  hom-inv-iso-Monoid :
    iso-Monoid → hom-Monoid N M
  hom-inv-iso-Monoid =
    hom-inv-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  map-inv-iso-Monoid :
    iso-Monoid → type-Monoid N → type-Monoid M
  map-inv-iso-Monoid f =
    map-hom-Monoid N M (hom-inv-iso-Monoid f)

  preserves-mul-inv-iso-Monoid :
    (f : iso-Monoid) {x y : type-Monoid N} →
    map-inv-iso-Monoid f (mul-Monoid N x y) ＝
    mul-Monoid M (map-inv-iso-Monoid f x) (map-inv-iso-Monoid f y)
  preserves-mul-inv-iso-Monoid f =
    preserves-mul-hom-Monoid N M (hom-inv-iso-Monoid f)

  is-section-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    comp-hom-Monoid N M N (hom-iso-Monoid f) (hom-inv-iso-Monoid f) ＝
    id-hom-Monoid N
  is-section-hom-inv-iso-Monoid =
    is-section-hom-inv-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-section-map-inv-iso-Monoid :
    (f : iso-Monoid) →
    map-iso-Monoid f ∘ map-inv-iso-Monoid f ~ id
  is-section-map-inv-iso-Monoid f =
    htpy-eq-hom-Monoid N N
      ( comp-hom-Monoid N M N (hom-iso-Monoid f) (hom-inv-iso-Monoid f))
      ( id-hom-Monoid N)
      ( is-section-hom-inv-iso-Monoid f)

  is-retraction-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    comp-hom-Monoid M N M (hom-inv-iso-Monoid f) (hom-iso-Monoid f) ＝
    id-hom-Monoid M
  is-retraction-hom-inv-iso-Monoid =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-retraction-map-inv-iso-Monoid :
    (f : iso-Monoid) →
    map-inv-iso-Monoid f ∘ map-iso-Monoid f ~ id
  is-retraction-map-inv-iso-Monoid f =
    htpy-eq-hom-Monoid M M
      ( comp-hom-Monoid M N M (hom-inv-iso-Monoid f) (hom-iso-Monoid f))
      ( id-hom-Monoid M)
      ( is-retraction-hom-inv-iso-Monoid f)
```

## Examples

### Identity homomorphisms are isomorphisms

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-iso-id-hom-Monoid :
    is-iso-Monoid M M (id-hom-Monoid M)
  is-iso-id-hom-Monoid =
    is-iso-id-hom-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}

  id-iso-Monoid : iso-Monoid M M
  id-iso-Monoid =
    id-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
```

### Equalities induce isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : Id x x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
iso-eq-Monoid :
  {l1 : Level} (M N : Monoid l1) → M ＝ N → iso-Monoid M N
iso-eq-Monoid = iso-eq-Large-Precategory Monoid-Large-Precategory
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are propositions
(since the hom-types are sets). But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'`.

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  is-prop-is-iso-Monoid :
    (f : hom-Monoid M N) →
    is-prop (is-iso-Monoid M N f)
  is-prop-is-iso-Monoid =
    is-prop-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
  is-iso-prop-Monoid :
    (f : hom-Monoid M N) → Prop (l1 ⊔ l2)
  is-iso-prop-Monoid =
    is-iso-prop-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  is-set-iso-Monoid : is-set (iso-Monoid M N)
  is-set-iso-Monoid =
    is-set-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  iso-set-Monoid : Set (l1 ⊔ l2)
  iso-set-Monoid =
    iso-set-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}
```

### Isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (M : Monoid l1) (N : Monoid l2) (K : Monoid l3)
  (g : iso-Monoid N K) (f : iso-Monoid M N)
  where

  hom-comp-iso-Monoid : hom-Monoid M K
  hom-comp-iso-Monoid =
    hom-comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  is-iso-comp-iso-Monoid :
    is-iso-Monoid M K hom-comp-iso-Monoid
  is-iso-comp-iso-Monoid =
    is-iso-comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  comp-iso-Monoid : iso-Monoid M K
  comp-iso-Monoid =
    comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : iso-Monoid M N)
  where

  is-iso-inv-iso-Monoid :
    is-iso-Monoid N M (hom-inv-iso-Monoid M N f)
  is-iso-inv-iso-Monoid =
    is-iso-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( is-iso-iso-Monoid M N f)

  inv-iso-Monoid : iso-Monoid N M
  inv-iso-Monoid =
    inv-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f
```

### Any isomorphism of monoids preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (f : iso-Monoid M N)
  where

  preserves-invertible-elements-iso-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid N (map-iso-Monoid M N f x)
  preserves-invertible-elements-iso-Monoid =
    preserves-invertible-elements-hom-Monoid M N (hom-iso-Monoid M N f)

  reflects-invertible-elements-iso-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid N (map-iso-Monoid M N f x) →
    is-invertible-element-Monoid M x
  reflects-invertible-elements-iso-Monoid H =
    tr
      ( is-invertible-element-Monoid M)
      ( is-retraction-map-inv-iso-Monoid M N f _)
      ( preserves-invertible-elements-hom-Monoid N M
        ( hom-inv-iso-Monoid M N f)
        ( H))
```

### Equivalences of monoids are equivalent to isomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (let
    G = semigroup-Monoid M
    H = semigroup-Monoid N)
  where

  equiv-iso-Monoid : iso-Monoid M N → type-Monoid M ≃ type-Monoid N
  pr1 (equiv-iso-Monoid i) =
    map-iso-Monoid M N i
  pr2 (equiv-iso-Monoid i) =
    is-equiv-is-invertible
      ( map-inv-iso-Monoid M N i)
      ( is-section-map-inv-iso-Monoid M N i)
      ( is-retraction-map-inv-iso-Monoid M N i)

  equiv-Monoid-iso-Monoid : iso-Monoid M N → equiv-Monoid M N
  pr1 (equiv-Monoid-iso-Monoid i) =
    ( equiv-iso-Monoid i , preserves-mul-iso-Monoid M N i)
  pr2 (equiv-Monoid-iso-Monoid i) =
    preserves-unit-hom-Monoid M N
      ( hom-iso-Monoid M N i)

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  is-equiv-prop-hom-Monoid : hom-Monoid M N → Prop (l1 ⊔ l2)
  is-equiv-prop-hom-Monoid f = is-equiv-Prop (map-hom-Monoid M N f)

  is-equiv-hom-Monoid : hom-Monoid M N → UU (l1 ⊔ l2)
  is-equiv-hom-Monoid f = type-Prop (is-equiv-prop-hom-Monoid f)

  equiv-Monoid' : UU (l1 ⊔ l2)
  equiv-Monoid' = Σ (hom-Monoid M N) is-equiv-hom-Monoid

  equiv-Monoid-equiv-Monoid' :
    equiv-Monoid' ≃ equiv-Monoid M N
  pr1 equiv-Monoid-equiv-Monoid' (((h , M) , H) , E) = ((h , E) , M) , H
  pr2 equiv-Monoid-equiv-Monoid' =
    is-equiv-is-invertible
      ( λ (((h , E) , M) , H) → ((h , M) , H) , E)
      ( refl-htpy)
      ( refl-htpy)

  is-equiv-is-iso-hom-Monoid :
    (f : hom-Monoid M N) → is-iso-Monoid M N f → is-equiv-hom-Monoid f
  is-equiv-is-iso-hom-Monoid f i =
    is-equiv-is-invertible
      ( map-hom-Monoid N M (hom-inv-is-iso-Monoid M N f i))
      ( λ x →
        ap
          ( λ p → pr1 (pr1 p) x)
          ( is-section-hom-inv-is-iso-Monoid M N f i))
          ( λ x →
              ap
                ( λ p → pr1 (pr1 p) x)
                ( is-retraction-hom-inv-is-iso-Monoid M N f i))

  is-iso-is-equiv-hom-Monoid :
    (f : hom-Monoid M N) → is-equiv-hom-Monoid f → is-iso-Monoid M N f
  is-iso-is-equiv-hom-Monoid f e =
    ( ( hom-inv-equiv-Monoid M N e') ,
      ( eq-pair-Σ
        ( eq-htpy-hom-Semigroup H H
          ( is-section-map-inv-equiv (equiv-equiv-Monoid M N e')))
        ( is-set-has-uip (is-set-type-Monoid N) _ _ _ _)) ,
      ( eq-pair-Σ
        ( eq-htpy-hom-Semigroup G G
          ( is-retraction-map-inv-equiv (equiv-equiv-Monoid M N e')))
        ( is-set-has-uip (is-set-type-Monoid M) _ _ _ _)))
    where
    e' = map-equiv equiv-Monoid-equiv-Monoid' (f , e)
    G = semigroup-Monoid M
    H = semigroup-Monoid N

  equiv-equiv-Monoid-iso-Monoid :
    equiv-Monoid' ≃ iso-Monoid M N
  equiv-equiv-Monoid-iso-Monoid =
    equiv-tot
      ( λ f →
        equiv-iff
          ( is-equiv-prop-hom-Monoid f)
          ( is-iso-prop-Monoid M N f)
          ( is-iso-is-equiv-hom-Monoid f)
          ( is-equiv-is-iso-hom-Monoid f))

  equiv-iso-equiv-Monoid : equiv-Monoid M N ≃ iso-Monoid M N
  equiv-iso-equiv-Monoid =
    equiv-equiv-Monoid-iso-Monoid ∘e inv-equiv equiv-Monoid-equiv-Monoid'

  iso-equiv-Monoid : equiv-Monoid M N → iso-Monoid M N
  iso-equiv-Monoid = map-equiv equiv-iso-equiv-Monoid

iso-extensionality-Monoid :
  {l : Level} (M N : Monoid l) → (M ＝ N) ≃ iso-Monoid M N
iso-extensionality-Monoid M N =
  equiv-iso-equiv-Monoid M N ∘e extensionality-Monoid M N
```

### Isomorphisms to `M` are torsorial

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-torsorial-iso-Monoid : is-torsorial (iso-Monoid M)
  is-torsorial-iso-Monoid =
    is-contr-equiv'
      ( Σ (Monoid l) (equiv-Monoid M))
      ( equiv-tot (equiv-iso-equiv-Monoid M))
      ( is-torsorial-equiv-Monoid M)
```
