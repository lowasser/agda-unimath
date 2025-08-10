# Sums of finite families of elements in abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-finite-families-of-elements-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.sums-of-finite-families-of-elements-commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of an abelian group" WD="sum" WDID=Q218005 Agda=sum-finite-Ab}}
extends the binary operation on an
[abelian group](group-theory.abelian-groups.md) `G` to any family of elements of
`G` indexed by a [finite type](univalent-combinatorics.finite-types.md).

## Sums over counted types

### Definition

```agda
sum-count-Ab :
  {l1 l2 : Level} (G : Ab l1) (A : UU l2) →
  count A → (A → type-Ab G) → type-Ab G
sum-count-Ab G = sum-count-Commutative-Monoid (commutative-monoid-Ab G)
```

### Properties

#### Sums for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : UU l2)
  where

  htpy-sum-count-Ab :
    (c : count A) → {f g : A → type-Ab G} → (f ~ g) →
    sum-count-Ab G A c f ＝ sum-count-Ab G A c g
  htpy-sum-count-Ab =
    htpy-sum-count-Commutative-Monoid (commutative-monoid-Ab G) A
```

#### Two counts for the same type produce equal sums

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : UU l2)
  where

  abstract
    eq-sum-count-equiv-Ab :
      (n : ℕ) → (equiv1 equiv2 : Fin n ≃ A) →
      (f : A → type-Ab G) →
      sum-count-Ab G A (n , equiv1) f ＝
      sum-count-Ab G A (n , equiv2) f
    eq-sum-count-equiv-Ab =
      eq-sum-count-equiv-Commutative-Monoid (commutative-monoid-Ab G) A

    eq-sum-count-Ab :
      (f : A → type-Ab G) (c1 c2 : count A) →
      sum-count-Ab G A c1 f ＝
      sum-count-Ab G A c2 f
    eq-sum-count-Ab =
      eq-sum-count-Commutative-Monoid (commutative-monoid-Ab G) A
```

#### Sums of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1)
  (A : UU l2) (B : UU l3) (H : A ≃ B)
  where

  abstract
    sum-equiv-count-Ab :
      (cA : count A) (cB : count B) (f : A → type-Ab G) →
      sum-count-Ab G A cA f ＝
      sum-count-Ab G B cB (f ∘ map-inv-equiv H)
    sum-equiv-count-Ab =
      sum-equiv-count-Commutative-Monoid (commutative-monoid-Ab G) A B H
```

## Sums over finite types

### Definition

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  where

  sum-finite-Ab :
    (f : type-Finite-Type A → type-Ab G) →
    type-Ab G
  sum-finite-Ab = sum-finite-Commutative-Monoid (commutative-monoid-Ab G) A
```

### Properties

#### The sum over a finite type is its sum over any count for the type

```agda
module _
  {l1 l2 : Level} (G : Ab l1)
  (A : Finite-Type l2) (cA : count (type-Finite-Type A))
  where

  abstract
    eq-sum-finite-sum-count-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      sum-finite-Ab G A f ＝
      sum-count-Ab G (type-Finite-Type A) cA f
    eq-sum-finite-sum-count-Ab =
      eq-sum-finite-sum-count-Commutative-Monoid (commutative-monoid-Ab G) A cA
```

#### The sum over an empty finite type is zero

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  abstract
    eq-zero-sum-finite-is-empty-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      is-zero-Ab G (sum-finite-Ab G A f)
    eq-zero-sum-finite-is-empty-Ab =
      eq-zero-sum-finite-is-empty-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
        ( H)
```

#### A sum of zeroes is zero

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  where

  sum-zero-finite-Ab :
    is-zero-Ab
      ( G)
      ( sum-finite-Ab
        ( G)
        ( A)
        ( λ _ → zero-Ab G))
  sum-zero-finite-Ab =
    sum-zero-finite-Commutative-Monoid (commutative-monoid-Ab G) A
```

#### Sums over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  where

  abstract
    htpy-sum-finite-Ab :
      {f g : type-Finite-Type A → type-Ab G} →
      f ~ g →
      sum-finite-Ab G A f ＝ sum-finite-Ab G A g
    htpy-sum-finite-Ab =
      htpy-sum-finite-Commutative-Monoid (commutative-monoid-Ab G) A
```

#### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  abstract
    sum-equiv-finite-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      sum-finite-Ab G A f ＝
      sum-finite-Ab G B (f ∘ map-inv-equiv H)
    sum-equiv-finite-Ab =
      sum-equiv-finite-Commutative-Monoid (commutative-monoid-Ab G) A B H
```

#### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  abstract
    distributive-distributive-sum-coproduct-finite-Ab :
      (f :
        type-Finite-Type A + type-Finite-Type B → type-Ab G) →
      sum-finite-Ab G (coproduct-Finite-Type A B) f ＝
      add-Ab
        ( G)
        ( sum-finite-Ab G A (f ∘ inl))
        ( sum-finite-Ab G B (f ∘ inr))
    distributive-distributive-sum-coproduct-finite-Ab =
      distributive-distributive-sum-coproduct-finite-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
        ( B)
```

#### Sums distribute over dependent pair types

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    sum-fin-finite-Σ-Ab :
      (n : ℕ) →
      {l2 : Level} →
      (B : Fin n → Finite-Type l2) →
      (f : (k : Fin n) → type-Finite-Type (B k) → type-Ab G) →
      sum-fin-sequence-type-Ab G n
        (λ k → sum-finite-Ab G (B k) (f k)) ＝
      sum-finite-Ab
        G (Σ-Finite-Type (Fin-Finite-Type n) B) (ind-Σ f)
    sum-fin-finite-Σ-Ab =
      sum-fin-finite-Σ-Commutative-Monoid (commutative-monoid-Ab G)

module _
  {l1 l2 l3 : Level} (G : Ab l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  abstract
    sum-Σ-finite-Ab :
      (f :
        (a : type-Finite-Type A) →
        type-Finite-Type (B a) →
        type-Ab G) →
      sum-finite-Ab G (Σ-Finite-Type A B) (ind-Σ f) ＝
      sum-finite-Ab
        ( G)
        ( A)
        ( λ a → sum-finite-Ab G (B a) (f a))
    sum-Σ-finite-Ab =
      sum-Σ-finite-Commutative-Monoid (commutative-monoid-Ab G) A B
```

#### Sums over the unit type

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    sum-finite-unit-type-Ab :
      (f : unit → type-Ab G) →
      sum-finite-Ab G unit-Finite-Type f ＝ f star
    sum-finite-unit-type-Ab =
      sum-finite-unit-type-Commutative-Monoid (commutative-monoid-Ab G)
```
