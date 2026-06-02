# Finite sequences in rings

```agda
module linear-algebra.finite-sequences-in-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.singleton-subtypes-discrete-types
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.sums-of-finite-families-of-elements-abelian-groups
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import linear-algebra.finite-sequences-in-semirings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import ring-theory.function-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.rings

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For any [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`,
and [ring](ring-theory.rings.md) `R`, the
{{#concept "left module of finite sequences" Disambiguation="in a ring" Agda=left-module-fin-sequence-Ring}}
of length `n` in `R` is the
`R`-[left-module](linear-algebra.left-modules-rings.md) of
[functions](ring-theory.function-rings.md) `Fin n → R`.

## Definitions

### The ring of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  ring-fin-sequence-Ring : Ring l
  ring-fin-sequence-Ring =
    function-Ring R (Fin n)
```

### The left module of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  left-module-fin-sequence-Ring : left-module-Ring l R
  left-module-fin-sequence-Ring =
    left-module-function-Ring R (Fin n)

  fin-sequence-type-Ring : UU l
  fin-sequence-type-Ring = fin-sequence (type-Ring R) n

  scalar-mul-fin-sequence-type-Ring :
    type-Ring R → fin-sequence-type-Ring → fin-sequence-type-Ring
  scalar-mul-fin-sequence-type-Ring =
    mul-left-module-Ring R left-module-fin-sequence-Ring
```

### Inherited algebraic structures on the type of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  ab-fin-sequence-type-Ring : Ab l
  ab-fin-sequence-type-Ring =
    ab-Ring (ring-fin-sequence-Ring R n)

  group-fin-sequence-type-Ring : Group l
  group-fin-sequence-type-Ring =
    group-Ab ab-fin-sequence-type-Ring

  semigroup-fin-sequence-type-Ring : Semigroup l
  semigroup-fin-sequence-type-Ring =
    semigroup-Ab ab-fin-sequence-type-Ring

  is-group-fin-sequence-type-Ring :
    is-group-Semigroup (semigroup-fin-sequence-type-Ring)
  is-group-fin-sequence-type-Ring =
    is-group-Ab ab-fin-sequence-type-Ring

  commutative-monoid-fin-sequence-type-Ring : Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Ring =
    commutative-monoid-Ab ab-fin-sequence-type-Ring

  monoid-fin-sequence-type-Ring : Monoid l
  monoid-fin-sequence-type-Ring =
    monoid-Ab ab-fin-sequence-type-Ring

  is-unital-fin-sequence-type-Ring :
    is-unital (add-Ab (ab-fin-sequence-type-Ring))
  is-unital-fin-sequence-type-Ring =
    is-unital-Monoid (monoid-fin-sequence-type-Ring)
```

### Constructors and accessors for finite sequences in rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  head-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R (succ-ℕ n) → type-Ring R
  head-fin-sequence-type-Ring n v = head-fin-sequence n v

  tail-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R (succ-ℕ n) → fin-sequence-type-Ring R n
  tail-fin-sequence-type-Ring = tail-fin-sequence

  cons-fin-sequence-type-Ring :
    (n : ℕ) → type-Ring R →
    fin-sequence-type-Ring R n → fin-sequence-type-Ring R (succ-ℕ n)
  cons-fin-sequence-type-Ring = cons-fin-sequence

  snoc-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R n → type-Ring R →
    fin-sequence-type-Ring R (succ-ℕ n)
  snoc-fin-sequence-type-Ring = snoc-fin-sequence
```

### The zero finite sequence in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-fin-sequence-type-Ring : (n : ℕ) → fin-sequence-type-Ring R n
  zero-fin-sequence-type-Ring = zero-Ring ∘ function-Ring R ∘ Fin
```

### Pointwise addition of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  add-fin-sequence-type-Ring = add-Ring ∘ function-Ring R ∘ Fin
```

### Pointwise negation of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  neg-fin-sequence-type-Ring = neg-Ring ∘ function-Ring R ∘ Fin
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-fin-sequence-type-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n
      ( add-fin-sequence-type-Ring R n v1 v2)
      ( v3) ＝
    add-fin-sequence-type-Ring R n v1 (add-fin-sequence-type-Ring R n v2 v3)
  associative-add-fin-sequence-type-Ring =
    associative-add-Ring ∘ function-Ring R ∘ Fin
```

### Unit laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (zero-fin-sequence-type-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-type-Ring =
    left-unit-law-add-Ring ∘ function-Ring R ∘ Fin

  right-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (zero-fin-sequence-type-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-type-Ring =
    right-unit-law-add-Ring ∘ function-Ring R ∘ Fin
```

### Commutativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v w ＝ add-fin-sequence-type-Ring R n w v
  commutative-add-fin-sequence-type-Ring =
    commutative-add-Ring ∘ function-Ring R ∘ Fin
```

### Inverse laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (neg-fin-sequence-type-Ring R n v) v ＝
    zero-fin-sequence-type-Ring R n
  left-inverse-law-add-fin-sequence-type-Ring =
    left-inverse-law-add-Ring ∘ function-Ring R ∘ Fin

  right-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (neg-fin-sequence-type-Ring R n v) ＝
    zero-fin-sequence-type-Ring R n
  right-inverse-law-add-fin-sequence-type-Ring =
    right-inverse-law-add-Ring ∘ function-Ring R ∘ Fin
```

### The coordinate homomorphisms

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ) (i : Fin n)
  where

  coordinate-hom-ring-fin-sequence-Ring :
    hom-Ring (ring-fin-sequence-Ring R n) R
  coordinate-hom-ring-fin-sequence-Ring =
    ev-hom-function-Ring R (Fin n) i

  coordinate-map-fin-sequence-Ring :
    fin-sequence-type-Ring R n → type-Ring R
  coordinate-map-fin-sequence-Ring =
    map-hom-Ring
      ( ring-fin-sequence-Ring R n)
      ( R)
      ( coordinate-hom-ring-fin-sequence-Ring)

  preserves-add-coordinate-map-fin-sequence-Ring :
    is-additive-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  preserves-add-coordinate-map-fin-sequence-Ring x y =
    preserves-add-hom-Ring
      ( ring-fin-sequence-Ring R n)
      ( R)
      ( coordinate-hom-ring-fin-sequence-Ring)
      { x}
      { y}

  is-homogeneous-coordinate-map-fin-sequence-Ring :
    is-homogeneous-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  is-homogeneous-coordinate-map-fin-sequence-Ring c x = refl

  is-linear-coordinate-map-fin-sequence-Ring :
    is-linear-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  is-linear-coordinate-map-fin-sequence-Ring =
    preserves-add-coordinate-map-fin-sequence-Ring ,
    is-homogeneous-coordinate-map-fin-sequence-Ring

  coordinate-linear-map-fin-sequence-Ring :
    linear-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
  coordinate-linear-map-fin-sequence-Ring =
    coordinate-map-fin-sequence-Ring ,
    is-linear-coordinate-map-fin-sequence-Ring
```

### Coordinates of sequence sums

```agda
abstract
  coordinate-sum-fin-sequence-fin-sequence-type-Ring :
    {l : Level} (R : Ring l) (m n : ℕ) (i : Fin n)
    (v : fin-sequence (fin-sequence-type-Ring R n) m) →
    sum-fin-sequence-type-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( m)
      ( v)
      ( i) ＝
    sum-fin-sequence-type-Ab (ab-Ring R) m (λ j → v j i)
  coordinate-sum-fin-sequence-fin-sequence-type-Ring R m n i =
    distributive-hom-sum-fin-sequence-type-Ab
      ( ab-left-module-Ring R (left-module-fin-sequence-Ring R n))
      ( ab-Ring R)
      ( hom-ab-linear-map-left-module-Ring R
        ( left-module-fin-sequence-Ring R n)
        ( left-module-ring-Ring R)
        ( coordinate-linear-map-fin-sequence-Ring R n i))
      ( m)
```

### The indicator sequence at a given index

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  indicator-fin-sequence-type-Ring :
    (i : Fin n) → fin-sequence-type-Ring R n
  indicator-fin-sequence-type-Ring i j =
    rec-coproduct
      ( λ _ → one-Ring R)
      ( λ _ → zero-Ring R)
      ( has-decidable-equality-Fin n i j)
```

### Every finite sequence in a ring is a linear combination of indicator sequences

```agda
abstract
  htpy-linear-combination-indicator-fin-sequence-type-Ring :
    {l : Level} (R : Ring l) (n : ℕ)
    (v : fin-sequence-type-Ring R n) →
    sum-fin-sequence-type-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Ring R n i)) ~
    v
  htpy-linear-combination-indicator-fin-sequence-type-Ring R n v k =
    equational-reasoning
      sum-fin-sequence-type-left-module-Ring R
        ( left-module-fin-sequence-Ring R n) n
        ( λ i →
          scalar-mul-fin-sequence-type-Ring R n (v i)
            ( indicator-fin-sequence-type-Ring R n i))
        ( k)
      ＝
        sum-fin-sequence-type-Ab
          ( ab-Ring R)
          ( n)
          ( λ j →
            scalar-mul-fin-sequence-type-Ring R n
              ( v j)
              ( indicator-fin-sequence-type-Ring R n j) k)
        by coordinate-sum-fin-sequence-fin-sequence-type-Ring R n n k _
      ＝
        sum-finite-Ab
          ( ab-Ring R)
          ( Fin-Finite-Type n)
          ( λ j →
            scalar-mul-fin-sequence-type-Ring R n
              ( v j)
              ( indicator-fin-sequence-type-Ring R n j) k)
        by
          inv
            ( eq-sum-finite-sum-count-Ab
              ( ab-Ring R)
              ( Fin-Finite-Type n)
              ( count-Fin n)
              ( _))
      ＝
        sum-finite-Ab (pr1 R)
          ( finite-type-subset-Finite-Type (Fin-Finite-Type n)
            ( decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( k)))
          ( λ (i , _) →
            mul-Ring R (v i) (indicator-fin-sequence-type-Ring R n i k))
        by
          vanish-sum-complement-decidable-subset-finite-Ab
            ( ab-Ring R)
            ( Fin-Finite-Type n)
            ( decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( k))
            ( _)
            ( λ i i≠k →
              equational-reasoning
                mul-Ring R
                  ( v i)
                  ( rec-coproduct
                    ( λ _ → one-Ring R)
                    ( λ _ → zero-Ring R)
                    ( has-decidable-equality-Fin n i k))
                ＝
                  mul-Ring R
                    ( v i)
                    ( zero-Ring R)
                  by
                    ap
                      ( mul-Ring R (v i) ∘ rec-coproduct _ _)
                      ( eq-is-prop'
                        ( is-prop-is-decidable (is-set-Fin n i k))
                        ( has-decidable-equality-Fin n i k)
                        ( inr i≠k))
                ＝ zero-Ring R
                  by right-zero-law-mul-Ring R (v i))
      ＝ mul-Ring R (v k) (indicator-fin-sequence-type-Ring R n k k)
        by
          sum-finite-is-contr-Ab
            ( ab-Ring R)
            ( _)
            ( is-contr-type-decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( k))
            ( k , refl)
            ( _)
      ＝ mul-Ring R (v k) (one-Ring R)
        by
          ap-mul-Ring R
            ( refl)
            ( ap
              ( rec-coproduct _ _)
              ( eq-is-prop'
                ( is-prop-is-decidable (is-set-Fin n k k))
                ( has-decidable-equality-Fin n k k)
                ( inl refl)))
      ＝ v k
        by right-unit-law-mul-Ring R (v k)

  eq-linear-combination-indicator-fin-sequence-type-Ring :
    {l : Level} (R : Ring l) (n : ℕ)
    (v : fin-sequence-type-Ring R n) →
    sum-fin-sequence-type-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Ring R n i)) ＝
    v
  eq-linear-combination-indicator-fin-sequence-type-Ring R n v =
    eq-htpy (htpy-linear-combination-indicator-fin-sequence-type-Ring R n v)
```
