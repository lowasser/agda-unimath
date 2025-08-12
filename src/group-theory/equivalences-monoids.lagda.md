# Equivalences between monoids

```agda
module group-theory.equivalences-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.unital-binary-operations
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.equivalences-semigroups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-semigroups
open import group-theory.monoids
```

</details>

## Idea

An {{#concept "equivalence" disambiguation="between monoids"}} between
[monoids](group-theory.monoids.md) is an
[equivalence](group-theory.equivalences-semigroups.md) between their underlying
[semigroups](group-theory.semigroups.md) that preserves the unit.

## Definition

### Equivalences of semigroups preserving units

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  preserves-unit-prop-equiv-Semigroup :
    equiv-Semigroup (semigroup-Monoid M) (semigroup-Monoid N) → Prop l2
  preserves-unit-prop-equiv-Semigroup e =
    Id-Prop
      ( set-Monoid N)
      ( pr1
        ( pr1 e)
        ( unit-Monoid M))
      ( unit-Monoid N)

  preserves-unit-equiv-Semigroup :
    equiv-Semigroup (semigroup-Monoid M) (semigroup-Monoid N) → UU l2
  preserves-unit-equiv-Semigroup e =
    type-Prop (preserves-unit-prop-equiv-Semigroup e)

  is-prop-preserves-unit-equit-Semigroup :
    (e : equiv-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)) →
    is-prop (preserves-unit-equiv-Semigroup e)
  is-prop-preserves-unit-equit-Semigroup e =
    is-prop-type-Prop (preserves-unit-prop-equiv-Semigroup e)

  equiv-Monoid : UU (l1 ⊔ l2)
  equiv-Monoid =
    Σ ( equiv-Semigroup (semigroup-Monoid M) (semigroup-Monoid N))
      ( preserves-unit-equiv-Semigroup)
```

### Components of an equivalence of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (e : equiv-Monoid M N)
  (let
    G = semigroup-Monoid M
    H = semigroup-Monoid N)
  where

  equiv-Semigroup-equiv-Monoid : equiv-Semigroup G H
  equiv-Semigroup-equiv-Monoid = pr1 e

  equiv-equiv-Monoid : type-Monoid M ≃ type-Monoid N
  equiv-equiv-Monoid = equiv-equiv-Semigroup G H equiv-Semigroup-equiv-Monoid

  inv-equiv-equiv-Monoid : type-Monoid N ≃ type-Monoid M
  inv-equiv-equiv-Monoid = inv-equiv equiv-equiv-Monoid

  preserves-unit-equiv-equiv-Monoid :
    preserves-unit-equiv-Semigroup M N equiv-Semigroup-equiv-Monoid
  preserves-unit-equiv-equiv-Monoid = pr2 e

  hom-Semigroup-equiv-Monoid : hom-Semigroup G H
  hom-Semigroup-equiv-Monoid =
    hom-equiv-Semigroup G H equiv-Semigroup-equiv-Monoid

  preserves-unit-hom-Semigroup-equiv-Monoid :
    preserves-unit-hom-Semigroup M N hom-Semigroup-equiv-Monoid
  preserves-unit-hom-Semigroup-equiv-Monoid = preserves-unit-equiv-equiv-Monoid

  map-equiv-Monoid : type-Monoid M → type-Monoid N
  map-equiv-Monoid = map-equiv-Semigroup G H equiv-Semigroup-equiv-Monoid

  map-inv-equiv-Monoid : type-Monoid N → type-Monoid M
  map-inv-equiv-Monoid = map-inv-equiv equiv-equiv-Monoid

  hom-equiv-Monoid : hom-Monoid M N
  pr1 hom-equiv-Monoid = hom-Semigroup-equiv-Monoid
  pr2 hom-equiv-Monoid = preserves-unit-hom-Semigroup-equiv-Monoid

  hom-inv-equiv-Monoid : hom-Monoid N M
  pr1 hom-inv-equiv-Monoid =
    hom-inv-equiv-Semigroup G H equiv-Semigroup-equiv-Monoid
  pr2 hom-inv-equiv-Monoid =
    map-inv-equiv-ap
      ( equiv-equiv-Monoid)
      ( _)
      ( _)
      ( ( is-section-map-inv-equiv
          ( equiv-equiv-Monoid)
          ( unit-Monoid N)) ∙
        ( inv preserves-unit-equiv-equiv-Monoid))
```

### The identity equivalence of monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  id-equiv-Monoid : equiv-Monoid M M
  pr1 id-equiv-Monoid = id-equiv-Semigroup (semigroup-Monoid M)
  pr2 id-equiv-Monoid = refl
```

### Characterization of identity types of monoids

```agda
module _

  {l : Level} (M : Monoid l)
  where

  equiv-eq-Monoid :
    (N : Monoid l) → M ＝ N → equiv-Monoid M N
  equiv-eq-Monoid .M refl = id-equiv-Monoid M

  abstract
    is-torsorial-preserves-unit-Monoid :
      is-torsorial
        ( λ (e : is-unital (mul-Monoid M)) →
          unit-Monoid M ＝ pr1 e)
    pr1 (pr1 is-torsorial-preserves-unit-Monoid) = has-unit-Monoid M
    pr2 (pr1 is-torsorial-preserves-unit-Monoid) = refl
    pr2 is-torsorial-preserves-unit-Monoid (e , E) =
      eq-pair-Σ
        ( eq-pair-Σ
          ( inv (pr1 (pr2 e) (unit-Monoid M)) ∙
            right-unit-law-mul-Monoid M (pr1 e))
          ( eq-pair-Σ
            ( eq-htpy (λ _ → is-set-has-uip (is-set-type-Monoid M) _ _ _ _))
            ( eq-htpy (λ _ → is-set-has-uip (is-set-type-Monoid M) _ _ _ _))))
        ( is-set-has-uip (is-set-type-Monoid M) _ _ _ _)

    is-torsorial-equiv-Monoid :
      is-torsorial (equiv-Monoid {l2 = l} M)
    is-torsorial-equiv-Monoid =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv-Semigroup (semigroup-Monoid M))
        ( semigroup-Monoid M , id-equiv-Semigroup (semigroup-Monoid M))
        ( is-torsorial-preserves-unit-Monoid)

    is-equiv-equiv-eq-Monoid :
      (N : Monoid l) → is-equiv (equiv-eq-Monoid N)
    is-equiv-equiv-eq-Monoid =
      fundamental-theorem-id
        ( is-torsorial-equiv-Monoid)
        ( equiv-eq-Monoid)

  extensionality-Monoid :
    (N : Monoid l) → (M ＝ N) ≃ equiv-Monoid M N
  extensionality-Monoid N = (equiv-eq-Monoid N , is-equiv-equiv-eq-Monoid N)

  eq-equiv-Monoid :
    (N : Monoid l) → equiv-Monoid M N → M ＝ N
  eq-equiv-Monoid N = map-inv-equiv (extensionality-Monoid N)
```
