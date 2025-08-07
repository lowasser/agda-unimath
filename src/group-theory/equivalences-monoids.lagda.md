# Equivalences between monoids

```agda
module group-theory.equivalences-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.equivalences-semigroups
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
```

</details>

## Idea

An equivalence between monoids is an [equivalence](foundation.equivalences.md)
between their underlying types that preserves the binary operation and the
identity.

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

  is-equiv-hom-Monoid : hom-Monoid M N → UU (l1 ⊔ l2)
  is-equiv-hom-Monoid f = is-equiv (map-hom-Monoid M N f)
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
    open import foundation.equality-dependent-pair-types
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
