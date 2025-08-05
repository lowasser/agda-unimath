# Isomorphisms of semirings

```agda
module ring-theory.isomorphisms-semirings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.iterated-dependent-product-types
open import foundation.multivariable-homotopies
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.isomorphisms-commutative-monoids
open import group-theory.isomorphisms-monoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.precategory-of-semirings
open import ring-theory.semirings
```

</details>

## Definition

### The predicate of being an isomorphism of semirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  is-iso-prop-Semiring : Prop (l1 ⊔ l2)
  is-iso-prop-Semiring =
    is-iso-prop-Large-Precategory Semiring-Large-Precategory {X = R} {Y = S} f

  is-iso-Semiring : UU (l1 ⊔ l2)
  is-iso-Semiring =
    is-iso-Large-Precategory Semiring-Large-Precategory {X = R} {Y = S} f

  is-prop-is-iso-Semiring : is-prop is-iso-Semiring
  is-prop-is-iso-Semiring =
    is-prop-is-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  hom-inv-is-iso-Semiring : is-iso-Semiring → hom-Semiring S R
  hom-inv-is-iso-Semiring =
    hom-inv-is-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  is-section-hom-inv-is-iso-Semiring :
    (U : is-iso-Semiring) →
    comp-hom-Semiring S R S f (hom-inv-is-iso-Semiring U) ＝ id-hom-Semiring S
  is-section-hom-inv-is-iso-Semiring =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  is-retraction-hom-inv-is-iso-Semiring :
    (U : is-iso-Semiring) →
    comp-hom-Semiring R S R (hom-inv-is-iso-Semiring U) f ＝ id-hom-Semiring R
  is-retraction-hom-inv-is-iso-Semiring =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  map-inv-is-iso-Semiring : is-iso-Semiring → type-Semiring S → type-Semiring R
  map-inv-is-iso-Semiring U =
    map-hom-Semiring S R (hom-inv-is-iso-Semiring U)

  is-section-map-inv-is-iso-Semiring :
    (U : is-iso-Semiring) → map-hom-Semiring R S f ∘ map-inv-is-iso-Semiring U ~ id
  is-section-map-inv-is-iso-Semiring U =
    htpy-eq-hom-Semiring S S
      ( comp-hom-Semiring S R S f (hom-inv-is-iso-Semiring U))
      ( id-hom-Semiring S)
      ( is-section-hom-inv-is-iso-Semiring U)

  is-retraction-map-inv-is-iso-Semiring :
    (U : is-iso-Semiring) → map-inv-is-iso-Semiring U ∘ map-hom-Semiring R S f ~ id
  is-retraction-map-inv-is-iso-Semiring U =
    htpy-eq-hom-Semiring R R
      ( comp-hom-Semiring R S R (hom-inv-is-iso-Semiring U) f)
      ( id-hom-Semiring R)
      ( is-retraction-hom-inv-is-iso-Semiring U)
```

### Isomorphisms of rings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  where

  iso-Semiring : UU (l1 ⊔ l2)
  iso-Semiring = iso-Large-Precategory Semiring-Large-Precategory R S

  hom-iso-Semiring : iso-Semiring → hom-Semiring R S
  hom-iso-Semiring =
    hom-iso-Large-Precategory Semiring-Large-Precategory {X = R} {Y = S}

  map-iso-Semiring : iso-Semiring → type-Semiring R → type-Semiring S
  map-iso-Semiring f = map-hom-Semiring R S (hom-iso-Semiring f)

  preserves-zero-iso-Semiring :
    (f : iso-Semiring) → map-iso-Semiring f (zero-Semiring R) ＝ zero-Semiring S
  preserves-zero-iso-Semiring f =
    preserves-zero-hom-Semiring R S (hom-iso-Semiring f)

  preserves-one-iso-Semiring :
    (f : iso-Semiring) → map-iso-Semiring f (one-Semiring R) ＝ one-Semiring S
  preserves-one-iso-Semiring f =
    preserves-one-hom-Semiring R S (hom-iso-Semiring f)

  preserves-add-iso-Semiring :
    (f : iso-Semiring) {x y : type-Semiring R} →
    map-iso-Semiring f (add-Semiring R x y) ＝
    add-Semiring S (map-iso-Semiring f x) (map-iso-Semiring f y)
  preserves-add-iso-Semiring f =
    preserves-add-hom-Semiring R S (hom-iso-Semiring f)

  preserves-mul-iso-Semiring :
    (f : iso-Semiring) {x y : type-Semiring R} →
    map-iso-Semiring f (mul-Semiring R x y) ＝
    mul-Semiring S (map-iso-Semiring f x) (map-iso-Semiring f y)
  preserves-mul-iso-Semiring f =
    preserves-mul-hom-Semiring R S (hom-iso-Semiring f)

  is-iso-iso-Semiring :
    (f : iso-Semiring) → is-iso-Semiring R S (hom-iso-Semiring f)
  is-iso-iso-Semiring =
    is-iso-iso-Large-Precategory Semiring-Large-Precategory {X = R} {Y = S}

  hom-inv-iso-Semiring : iso-Semiring → hom-Semiring S R
  hom-inv-iso-Semiring =
    hom-inv-iso-Large-Precategory Semiring-Large-Precategory {X = R} {Y = S}

  map-inv-iso-Semiring : iso-Semiring → type-Semiring S → type-Semiring R
  map-inv-iso-Semiring f = map-hom-Semiring S R (hom-inv-iso-Semiring f)

  preserves-zero-inv-iso-Semiring :
    (f : iso-Semiring) → map-inv-iso-Semiring f (zero-Semiring S) ＝ zero-Semiring R
  preserves-zero-inv-iso-Semiring f =
    preserves-zero-hom-Semiring S R (hom-inv-iso-Semiring f)

  preserves-one-inv-iso-Semiring :
    (f : iso-Semiring) → map-inv-iso-Semiring f (one-Semiring S) ＝ one-Semiring R
  preserves-one-inv-iso-Semiring f =
    preserves-one-hom-Semiring S R (hom-inv-iso-Semiring f)

  preserves-add-inv-iso-Semiring :
    (f : iso-Semiring) {x y : type-Semiring S} →
    map-inv-iso-Semiring f (add-Semiring S x y) ＝
    add-Semiring R (map-inv-iso-Semiring f x) (map-inv-iso-Semiring f y)
  preserves-add-inv-iso-Semiring f =
    preserves-add-hom-Semiring S R (hom-inv-iso-Semiring f)

  preserves-mul-inv-iso-Semiring :
    (f : iso-Semiring) {x y : type-Semiring S} →
    map-inv-iso-Semiring f (mul-Semiring S x y) ＝
    mul-Semiring R (map-inv-iso-Semiring f x) (map-inv-iso-Semiring f y)
  preserves-mul-inv-iso-Semiring f =
    preserves-mul-hom-Semiring S R (hom-inv-iso-Semiring f)

  is-section-hom-inv-iso-Semiring :
    (f : iso-Semiring) →
    comp-hom-Semiring S R S (hom-iso-Semiring f) (hom-inv-iso-Semiring f) ＝ id-hom-Semiring S
  is-section-hom-inv-iso-Semiring =
    is-section-hom-inv-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}

  is-section-map-inv-iso-Semiring :
    (f : iso-Semiring) → map-iso-Semiring f ∘ map-inv-iso-Semiring f ~ id
  is-section-map-inv-iso-Semiring f =
    htpy-eq-hom-Semiring S S
      ( comp-hom-Semiring S R S (hom-iso-Semiring f) (hom-inv-iso-Semiring f))
      ( id-hom-Semiring S)
      ( is-section-hom-inv-iso-Semiring f)

  is-retraction-hom-inv-iso-Semiring :
    (f : iso-Semiring) →
    comp-hom-Semiring R S R (hom-inv-iso-Semiring f) (hom-iso-Semiring f) ＝ id-hom-Semiring R
  is-retraction-hom-inv-iso-Semiring =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Semiring-Large-Precategory)
      { X = R}
      { Y = S}

  is-retraction-map-inv-iso-Semiring :
    (f : iso-Semiring) → map-inv-iso-Semiring f ∘ map-iso-Semiring f ~ id
  is-retraction-map-inv-iso-Semiring f =
    htpy-eq-hom-Semiring R R
      ( comp-hom-Semiring R S R (hom-inv-iso-Semiring f) (hom-iso-Semiring f))
      ( id-hom-Semiring R)
      ( is-retraction-hom-inv-iso-Semiring f)

  iso-multiplicative-monoid-iso-Semiring :
    (f : iso-Semiring) →
    iso-Monoid (multiplicative-monoid-Semiring R) (multiplicative-monoid-Semiring S)
  pr1 (iso-multiplicative-monoid-iso-Semiring f) =
    hom-multiplicative-monoid-hom-Semiring R S (hom-iso-Semiring f)
  pr1 (pr2 (iso-multiplicative-monoid-iso-Semiring f)) =
    hom-multiplicative-monoid-hom-Semiring S R (hom-inv-iso-Semiring f)
  pr1 (pr2 (pr2 (iso-multiplicative-monoid-iso-Semiring f))) =
    eq-htpy-hom-Monoid
      ( multiplicative-monoid-Semiring S)
      ( multiplicative-monoid-Semiring S)
      ( comp-hom-Monoid
        ( multiplicative-monoid-Semiring S)
        ( multiplicative-monoid-Semiring R)
        ( multiplicative-monoid-Semiring S)
        ( hom-multiplicative-monoid-hom-Semiring R S (hom-iso-Semiring f))
        ( hom-multiplicative-monoid-hom-Semiring S R (hom-inv-iso-Semiring f)))
      ( id-hom-Monoid (multiplicative-monoid-Semiring S))
      ( is-section-map-inv-iso-Semiring f)
  pr2 (pr2 (pr2 (iso-multiplicative-monoid-iso-Semiring f))) =
    eq-htpy-hom-Monoid
      ( multiplicative-monoid-Semiring R)
      ( multiplicative-monoid-Semiring R)
      ( comp-hom-Monoid
        ( multiplicative-monoid-Semiring R)
        ( multiplicative-monoid-Semiring S)
        ( multiplicative-monoid-Semiring R)
        ( hom-multiplicative-monoid-hom-Semiring S R (hom-inv-iso-Semiring f))
        ( hom-multiplicative-monoid-hom-Semiring R S (hom-iso-Semiring f)))
      ( id-hom-Monoid (multiplicative-monoid-Semiring R))
      ( is-retraction-map-inv-iso-Semiring f)
```

### The identity isomorphism of rings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-iso-id-hom-Semiring : is-iso-Semiring R R (id-hom-Semiring R)
  is-iso-id-hom-Semiring =
    is-iso-id-hom-Large-Precategory Semiring-Large-Precategory {X = R}

  id-iso-Semiring : iso-Semiring R R
  pr1 id-iso-Semiring = id-hom-Semiring R
  pr2 id-iso-Semiring = is-iso-id-hom-Semiring
```

### Converting identifications of rings to isomorphisms of rings

```agda
iso-eq-Semiring :
  { l : Level} (R S : Semiring l) → R ＝ S → iso-Semiring R S
iso-eq-Semiring R S = iso-eq-Large-Precategory Semiring-Large-Precategory R S
```

## Properties

### A semiring homomorphism is an isomorphism if and only if the underlying homomorphism of commutative monoids is an isomorphism

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  where

  iso-additive-commutative-monoid-Semiring : UU (l1 ⊔ l2)
  iso-additive-commutative-monoid-Semiring =
    Σ ( iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S))
      ( λ f →
        is-semiring-homomorphism-hom-Commutative-Monoid R S
          ( hom-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( f)))

  iso-additive-commutative-monoid-iso-additive-commutative-monoid-Semiring :
    iso-additive-commutative-monoid-Semiring →
    iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
  iso-additive-commutative-monoid-iso-additive-commutative-monoid-Semiring = pr1

  is-iso-additive-commutative-monoid-hom-Semiring :
    hom-Semiring R S → UU (l1 ⊔ l2)
  is-iso-additive-commutative-monoid-hom-Semiring f =
    is-iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
      ( hom-additive-commutative-monoid-hom-Semiring R S f)

  is-iso-additive-commutative-monoid-is-iso-Semiring :
    (f : hom-Semiring R S) →
    is-iso-Semiring R S f → is-iso-additive-commutative-monoid-hom-Semiring f
  pr1 (is-iso-additive-commutative-monoid-is-iso-Semiring f U) =
    hom-additive-commutative-monoid-hom-Semiring S R
      ( hom-inv-is-iso-Semiring R S f U)
  pr1 (pr2 (is-iso-additive-commutative-monoid-is-iso-Semiring f U)) =
    ap
      ( hom-additive-commutative-monoid-hom-Semiring S S)
      ( is-section-hom-inv-is-iso-Semiring R S f U)
  pr2 (pr2 (is-iso-additive-commutative-monoid-is-iso-Semiring f U)) =
    ap
      ( hom-additive-commutative-monoid-hom-Semiring R R)
      ( is-retraction-hom-inv-is-iso-Semiring R S f U)

  abstract
    preserves-mul-inv-is-iso-Commutative-Monoid :
      (f :
        hom-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S)) →
      (U :
        is-iso-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S)
          ( f)) →
      preserves-mul-hom-additive-commutative-monoid-Semiring R S f →
      preserves-mul-hom-additive-commutative-monoid-Semiring S R
        ( hom-inv-is-iso-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S)
          ( f)
          ( U))
    preserves-mul-inv-is-iso-Commutative-Monoid f U μ {x} {y} =
      ( inv
        ( ap
          ( map-inv-is-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( f)
            ( U))
          ( ( μ) ∙
            ( ap-mul-Semiring S
              ( is-section-map-inv-is-iso-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( additive-commutative-monoid-Semiring S)
                ( f)
                ( U)
                ( x))
              ( is-section-map-inv-is-iso-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( additive-commutative-monoid-Semiring S)
                ( f)
                ( U)
                ( y)))))) ∙
      ( is-retraction-map-inv-is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( f)
        ( U)
        ( mul-Semiring R
          ( map-inv-is-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( f)
            ( U)
            ( x))
          ( map-inv-is-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( f)
            ( U)
            ( y))))

  preserves-unit-inv-is-iso-Commutative-Monoid :
    (f :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)) →
    (U :
      is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( f)) →
    preserves-unit-hom-additive-commutative-monoid-Semiring R S f →
    preserves-unit-hom-additive-commutative-monoid-Semiring S R
      ( hom-inv-is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( f)
        ( U))
  preserves-unit-inv-is-iso-Commutative-Monoid f U ν =
    ( inv
      ( ap
        ( map-inv-is-iso-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S)
          ( f)
          ( U))
        ( ν))) ∙
    ( is-retraction-map-inv-is-iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
      ( f)
      ( U)
      ( _))

  is-ring-homomorphism-inv-is-iso-Commutative-Monoid :
    (f :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)) →
    (U :
      is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( f)) →
    is-semiring-homomorphism-hom-Commutative-Monoid R S f →
    is-semiring-homomorphism-hom-Commutative-Monoid S R
      ( hom-inv-is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( f)
        ( U))
  pr1 (is-ring-homomorphism-inv-is-iso-Commutative-Monoid f U (μ , ν)) =
    preserves-mul-inv-is-iso-Commutative-Monoid f U μ
  pr2 (is-ring-homomorphism-inv-is-iso-Commutative-Monoid f U (μ , ν)) =
    preserves-unit-inv-is-iso-Commutative-Monoid f U ν

  inv-hom-ring-is-iso-Commutative-Monoid :
    (f : hom-Semiring R S) →
    is-iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
      ( hom-additive-commutative-monoid-hom-Semiring R S f) →
    hom-Semiring S R
  pr1 (inv-hom-ring-is-iso-Commutative-Monoid f U) =
    hom-inv-is-iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
      ( hom-additive-commutative-monoid-hom-Semiring R S f)
      ( U)
  pr2 (inv-hom-ring-is-iso-Commutative-Monoid f U) =
    is-ring-homomorphism-inv-is-iso-Commutative-Monoid
      ( hom-additive-commutative-monoid-hom-Semiring R S f)
      ( U)
      ( is-semiring-homomorphism-hom-Semiring R S f)

  abstract
    is-iso-ring-is-iso-Commutative-Monoid :
      (f : hom-Semiring R S) →
      is-iso-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
        ( hom-additive-commutative-monoid-hom-Semiring R S f) →
      is-iso-Semiring R S f
    pr1 (is-iso-ring-is-iso-Commutative-Monoid f U) =
      inv-hom-ring-is-iso-Commutative-Monoid f U
    pr1 (pr2 (is-iso-ring-is-iso-Commutative-Monoid f U)) =
      eq-htpy-hom-Semiring S S
        ( comp-hom-Semiring S R S f
          ( inv-hom-ring-is-iso-Commutative-Monoid f U))
        ( id-hom-Semiring S)
        ( htpy-eq-hom-Commutative-Monoid
          ( additive-commutative-monoid-Semiring S)
          ( additive-commutative-monoid-Semiring S)
          ( hom-additive-commutative-monoid-hom-Semiring S S
            ( comp-hom-Semiring S R S f
              ( inv-hom-ring-is-iso-Commutative-Monoid f U)))
          ( id-hom-Commutative-Monoid (additive-commutative-monoid-Semiring S))
          ( is-section-hom-inv-is-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( hom-additive-commutative-monoid-hom-Semiring R S f)
            ( U)))
    pr2 (pr2 (is-iso-ring-is-iso-Commutative-Monoid f U)) =
      eq-htpy-hom-Semiring R R
        ( comp-hom-Semiring R S R
          ( inv-hom-ring-is-iso-Commutative-Monoid f U)
          ( f))
        ( id-hom-Semiring R)
        ( htpy-eq-hom-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring R)
          ( hom-additive-commutative-monoid-hom-Semiring R R
            ( comp-hom-Semiring R S R
              ( inv-hom-ring-is-iso-Commutative-Monoid f U)
              ( f)))
          ( id-hom-Commutative-Monoid (additive-commutative-monoid-Semiring R))
          ( is-retraction-hom-inv-is-iso-Commutative-Monoid
            ( additive-commutative-monoid-Semiring R)
            ( additive-commutative-monoid-Semiring S)
            ( hom-additive-commutative-monoid-hom-Semiring R S f)
            ( U)))

  iso-additive-commutative-monoid-iso-Semiring :
    iso-Semiring R S →
    iso-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)
  pr1 (iso-additive-commutative-monoid-iso-Semiring f) =
    hom-additive-commutative-monoid-hom-Semiring R S (hom-iso-Semiring R S f)
  pr2 (iso-additive-commutative-monoid-iso-Semiring f) =
    is-iso-additive-commutative-monoid-is-iso-Semiring
      ( hom-iso-Semiring R S f)
      ( is-iso-iso-Semiring R S f)

  equiv-iso-ab-iso-Semiring :
    iso-Semiring R S ≃ iso-additive-commutative-monoid-Semiring
  equiv-iso-ab-iso-Semiring =
    ( inv-equiv
      ( associative-Σ
        ( hom-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S))
        ( is-iso-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( additive-commutative-monoid-Semiring S))
        ( λ f →
          is-semiring-homomorphism-hom-Commutative-Monoid R S (pr1 f)))) ∘e
          equiv-tot (λ f → commutative-product) ∘e
          ( associative-Σ
            ( hom-Commutative-Monoid
              ( additive-commutative-monoid-Semiring R)
              ( additive-commutative-monoid-Semiring S))
            ( is-semiring-homomorphism-hom-Commutative-Monoid R S)
            ( λ f →
              is-iso-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( additive-commutative-monoid-Semiring S) (pr1 f))) ∘e
          ( equiv-type-subtype
            ( is-prop-is-iso-Semiring R S)
            ( λ f →
              is-prop-is-iso-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( additive-commutative-monoid-Semiring S)
                ( hom-additive-commutative-monoid-hom-Semiring R S f))
            ( is-iso-additive-commutative-monoid-is-iso-Semiring)
            ( is-iso-ring-is-iso-Commutative-Monoid))
```

### Characterizing identifications of semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    is-torsorial-iso-Semiring :
      is-torsorial (λ (S : Semiring l) → iso-Semiring R S)
    is-torsorial-iso-Semiring =
      is-contr-equiv
        ( Σ (Semiring l) (iso-additive-commutative-monoid-Semiring R))
        ( equiv-tot (equiv-iso-ab-iso-Semiring R))
        ( is-torsorial-Eq-structure
          ( is-torsorial-iso-Commutative-Monoid (additive-commutative-monoid-Semiring R))
          ( additive-commutative-monoid-Semiring R , id-iso-Ab (additive-commutative-monoid-Semiring R))
          ( is-torsorial-Eq-structure
            ( is-torsorial-Eq-subtype
              ( is-torsorial-multivariable-implicit-htpy 2 (mul-Semiring R))
              ( λ μ →
                is-prop-iterated-Π 3
                  ( λ x y z → is-set-type-Semiring R (μ (μ x y) z) (μ x (μ y z))))
              ( mul-Semiring R)
              ( λ {x} {y} → refl)
              ( associative-mul-Semiring R))
            ( (mul-Semiring R , associative-mul-Semiring R) , λ {x} {y} → refl)
            ( is-torsorial-Eq-subtype
              ( is-torsorial-Eq-subtype
                ( is-torsorial-Id (one-Semiring R))
                ( λ x →
                  is-prop-product
                    ( is-prop-Π (λ y → is-set-type-Semiring R (mul-Semiring R x y) y))
                    ( is-prop-Π (λ y → is-set-type-Semiring R (mul-Semiring R y x) y)))
                ( one-Semiring R)
                ( refl)
                ( left-unit-law-mul-Semiring R , right-unit-law-mul-Semiring R))
              ( λ u →
                is-prop-product
                  ( is-prop-iterated-Π 3
                    ( λ x y z →
                      is-set-type-Semiring R
                        ( mul-Semiring R x (add-Semiring R y z))
                        ( add-Semiring R (mul-Semiring R x y) (mul-Semiring R x z))))
                  ( is-prop-iterated-Π 3
                    ( λ x y z →
                      is-set-type-Semiring R
                        ( mul-Semiring R (add-Semiring R x y) z)
                        ( add-Semiring R (mul-Semiring R x z) (mul-Semiring R y z)))))
              ( is-unital-Semiring R)
              ( refl)
              ( left-distributive-mul-add-Semiring R ,
                right-distributive-mul-add-Semiring R))))

  is-equiv-iso-eq-Semiring :
    (S : Semiring l) → is-equiv (iso-eq-Semiring R S)
  is-equiv-iso-eq-Semiring =
    fundamental-theorem-id
      ( is-torsorial-iso-Semiring)
      ( iso-eq-Semiring R)

  extensionality-Semiring : (S : Semiring l) → (R ＝ S) ≃ iso-Semiring R S
  pr1 (extensionality-Semiring S) = iso-eq-Semiring R S
  pr2 (extensionality-Semiring S) = is-equiv-iso-eq-Semiring S

  eq-iso-Semiring : (S : Semiring l) → iso-Semiring R S → R ＝ S
  eq-iso-Semiring S = map-inv-is-equiv (is-equiv-iso-eq-Semiring S)
```

### Any ring isomorphism preserves and reflects invertible elements

```agda
{- module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : iso-Semiring R S)
  where

  preserves-invertible-elements-iso-Semiring :
    {x : type-Semiring R} →
    is-invertible-element-Semiring R x →
    is-invertible-element-Semiring S (map-iso-Semiring R S f x)
  preserves-invertible-elements-iso-Semiring =
    preserves-invertible-elements-iso-Monoid
      ( multiplicative-monoid-Semiring R)
      ( multiplicative-monoid-Semiring S)
      ( iso-multiplicative-monoid-iso-Semiring R S f)

  reflects-invertible-elements-iso-Semiring :
    {x : type-Semiring R} →
    is-invertible-element-Semiring S (map-iso-Semiring R S f x) →
    is-invertible-element-Semiring R x
  reflects-invertible-elements-iso-Semiring =
    reflects-invertible-elements-iso-Monoid
      ( multiplicative-monoid-Semiring R)
      ( multiplicative-monoid-Semiring S)
      ( iso-multiplicative-monoid-iso-Semiring R S f)-}
```
