# Equivalences between semigroups

```agda
module group-theory.equivalences-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

An equivalence between semigroups is an equivalence between their underlying
types that preserves the binary operation.

## Definition

### Equivalences preserving binary operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv μA μB e = preserves-mul μA μB (map-equiv e)
```

### Equivalences of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup e =
    preserves-mul-equiv (mul-Semigroup G) (mul-Semigroup H) e

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup =
    Σ (type-Semigroup G ≃ type-Semigroup H) preserves-mul-equiv-Semigroup

  is-equiv-hom-Semigroup : hom-Semigroup G H → UU (l1 ⊔ l2)
  is-equiv-hom-Semigroup f = is-equiv (map-hom-Semigroup G H f)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (e : equiv-Semigroup G H)
  where

  equiv-equiv-Semigroup : type-Semigroup G ≃ type-Semigroup H
  equiv-equiv-Semigroup = pr1 e

  map-equiv-Semigroup : type-Semigroup G → type-Semigroup H
  map-equiv-Semigroup = map-equiv equiv-equiv-Semigroup

  is-equiv-map-equiv-Semigroup : is-equiv map-equiv-Semigroup
  is-equiv-map-equiv-Semigroup = is-equiv-map-equiv equiv-equiv-Semigroup

  preserves-mul-equiv-equiv-Semigroup :
    preserves-mul-equiv-Semigroup G H equiv-equiv-Semigroup
  preserves-mul-equiv-equiv-Semigroup = pr2 e

  preserves-mul-map-equiv-Semigroup :
    preserves-mul-Semigroup G H map-equiv-Semigroup
  preserves-mul-map-equiv-Semigroup = preserves-mul-equiv-equiv-Semigroup

  hom-equiv-Semigroup : hom-Semigroup G H
  pr1 hom-equiv-Semigroup = map-equiv-Semigroup
  pr2 hom-equiv-Semigroup = preserves-mul-map-equiv-Semigroup

  inv-equiv-equiv-Semigroup : type-Semigroup H ≃ type-Semigroup G
  inv-equiv-equiv-Semigroup = inv-equiv equiv-equiv-Semigroup

  map-inv-equiv-equiv-Semigroup : type-Semigroup H → type-Semigroup G
  map-inv-equiv-equiv-Semigroup = map-equiv inv-equiv-equiv-Semigroup
```

## Properties

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : hom-Semigroup G H)
      ( U : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv U)
    preserves-mul-map-inv-is-equiv-Semigroup (f , μ-f) U {x} {y} =
      map-inv-is-equiv
        ( is-emb-is-equiv U
          ( map-inv-is-equiv U (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv U x)
            ( map-inv-is-equiv U y)))
        ( ( is-section-map-inv-is-equiv U (mul-Semigroup H x y)) ∙
          ( ap
            ( λ t → mul-Semigroup H t y)
            ( inv (is-section-map-inv-is-equiv U x))) ∙
          ( ap
            ( mul-Semigroup H (f (map-inv-is-equiv U x)))
            ( inv (is-section-map-inv-is-equiv U y))) ∙
          ( inv μ-f))

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (e : equiv-Semigroup G H)
  where

  preserves-mul-map-inv-equiv-Semigroup :
    preserves-mul-Semigroup H G (map-inv-equiv-equiv-Semigroup G H e)
  preserves-mul-map-inv-equiv-Semigroup =
    preserves-mul-map-inv-is-equiv-Semigroup G H
      ( hom-equiv-Semigroup G H e)
      ( is-equiv-map-equiv-Semigroup G H e)

  hom-inv-equiv-Semigroup : hom-Semigroup H G
  pr1 hom-inv-equiv-Semigroup = map-inv-equiv-equiv-Semigroup G H e
  pr2 hom-inv-equiv-Semigroup = preserves-mul-map-inv-equiv-Semigroup
```

### The identity equivalence of semigroups

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  id-equiv-Semigroup : equiv-Semigroup G G
  pr1 id-equiv-Semigroup = id-equiv
  pr2 id-equiv-Semigroup = refl
```

### The total space of all equivalences of semigroups with domain `G` is contractible

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = mul-Semigroup G
  pr2 (pr1 (center-total-preserves-mul-id-Semigroup)) =
    associative-mul-Semigroup G
  pr2 (center-total-preserves-mul-id-Semigroup) = refl

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    Id center-total-preserves-mul-id-Semigroup t
  contraction-total-preserves-mul-id-Semigroup
    ( (μ-G' , associative-G') , μ-id) =
    eq-type-subtype
      ( λ μ →
        preserves-mul-prop-Semigroup G (pair (set-Semigroup G) μ) id)
      ( eq-type-subtype
        ( λ μ →
          Π-Prop
            ( type-Semigroup G)
            ( λ x →
              Π-Prop
                ( type-Semigroup G)
                ( λ y →
                  Π-Prop
                    ( type-Semigroup G)
                    ( λ z →
                      Id-Prop
                        ( set-Semigroup G)
                        ( μ (μ x y) z) (μ x (μ y z))))))
        ( eq-htpy (λ x → eq-htpy (λ y → μ-id))))

  is-torsorial-preserves-mul-id-Semigroup :
    is-torsorial
      ( λ (μ : has-associative-mul (type-Semigroup G)) →
        preserves-mul (mul-Semigroup G) (pr1 μ) id)
  pr1 is-torsorial-preserves-mul-id-Semigroup =
    center-total-preserves-mul-id-Semigroup
  pr2 is-torsorial-preserves-mul-id-Semigroup =
    contraction-total-preserves-mul-id-Semigroup

  is-torsorial-equiv-Semigroup :
    is-torsorial (equiv-Semigroup G)
  is-torsorial-equiv-Semigroup =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv (type-Semigroup G))
        ( is-prop-is-set)
        ( type-Semigroup G)
        ( id-equiv)
        ( is-set-type-Semigroup G))
      ( pair (set-Semigroup G) id-equiv)
      ( is-torsorial-preserves-mul-id-Semigroup)
```
