# Finite sequences in groups

```agda
module linear-algebra.finite-sequences-in-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
```

</details>

## Idea

Given a [group](group-theory.groups.md) `G`, the type `fin-sequence n G` of
[finite sequences](lists.finite-sequences.md) of length `n` of elements of `G`
is a group given by componentwise multiplication.

We use additive terminology for finite sequences, as is standard in linear
algebra contexts, despite using multiplicative terminology for groups.

## Definitions

```agda
module _
  {l : Level} (G : Group l)
  where

  fin-sequence-type-Group : ℕ → UU l
  fin-sequence-type-Group = fin-sequence (type-Group G)

  head-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group (succ-ℕ n) → type-Group G
  head-fin-sequence-type-Group n v = head-fin-sequence n v

  tail-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group (succ-ℕ n) → fin-sequence-type-Group n
  tail-fin-sequence-type-Group = tail-fin-sequence

  cons-fin-sequence-type-Group :
    (n : ℕ) → type-Group G →
    fin-sequence-type-Group n → fin-sequence-type-Group (succ-ℕ n)
  cons-fin-sequence-type-Group = cons-fin-sequence

  snoc-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group n → type-Group G →
    fin-sequence-type-Group (succ-ℕ n)
  snoc-fin-sequence-type-Group = snoc-fin-sequence
```

### The finite sequence of zeros in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  zero-fin-sequence-type-Group : (n : ℕ) → fin-sequence-type-Group G n
  zero-fin-sequence-type-Group n i = unit-Group G
```

### Negation of finite sequences in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  neg-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group G n → fin-sequence-type-Group G n
  neg-fin-sequence-type-Group n f i = inv-Group G (f i)
```

### Pointwise addition of finite sequences in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  add-fin-sequence-type-Group :
    (n : ℕ) (v w : fin-sequence-type-Group G n) → fin-sequence-type-Group G n
  add-fin-sequence-type-Group n = binary-map-fin-sequence n (mul-Group G)

  associative-add-fin-sequence-type-Group :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Group G n) →
    ( add-fin-sequence-type-Group n
      ( add-fin-sequence-type-Group n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-type-Group n v1 (add-fin-sequence-type-Group n v2 v3))
  associative-add-fin-sequence-type-Group n v1 v2 v3 =
    eq-htpy (λ i → associative-mul-Group G (v1 i) (v2 i) (v3 i))

  semigroup-fin-sequence-type-Group : ℕ → Semigroup l
  pr1 (semigroup-fin-sequence-type-Group n) =
    fin-sequence-Set (set-Group G) n
  pr1 (pr2 (semigroup-fin-sequence-type-Group n)) =
    add-fin-sequence-type-Group n
  pr2 (pr2 (semigroup-fin-sequence-type-Group n)) =
    associative-add-fin-sequence-type-Group n

  left-unit-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n (zero-fin-sequence-type-Group G n) v ＝ v
  left-unit-law-add-fin-sequence-type-Group n v =
    eq-htpy (λ i → left-unit-law-mul-Group G (v i))

  right-unit-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n v (zero-fin-sequence-type-Group G n) ＝ v
  right-unit-law-add-fin-sequence-type-Group n v =
    eq-htpy (λ i → right-unit-law-mul-Group G (v i))

  is-unital-add-fin-sequence-type-Group :
    (n : ℕ) → is-unital (add-fin-sequence-type-Group n)
  is-unital-add-fin-sequence-type-Group n =
    ( zero-fin-sequence-type-Group G n ,
      left-unit-law-add-fin-sequence-type-Group n ,
      right-unit-law-add-fin-sequence-type-Group n)

  monoid-fin-sequence-type-Group : ℕ → Monoid l
  monoid-fin-sequence-type-Group n =
    ( semigroup-fin-sequence-type-Group n ,
      is-unital-add-fin-sequence-type-Group n)

  left-inverse-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group
      ( n)
      ( neg-fin-sequence-type-Group G n v)
      ( v) ＝
    zero-fin-sequence-type-Group G n
  left-inverse-law-add-fin-sequence-type-Group _ _ =
    eq-htpy (λ _ → left-inverse-law-mul-Group G _)

  right-inverse-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group
      ( n)
      ( v)
      ( neg-fin-sequence-type-Group G n v) ＝
    zero-fin-sequence-type-Group G n
  right-inverse-law-add-fin-sequence-type-Group _ _ =
    eq-htpy (λ _ → right-inverse-law-mul-Group G _)

  group-fin-sequence-type-Group : (n : ℕ) → Group l
  group-fin-sequence-type-Group n =
    ( semigroup-fin-sequence-type-Group n ,
      is-unital-add-fin-sequence-type-Group n ,
      neg-fin-sequence-type-Group G n ,
      left-inverse-law-add-fin-sequence-type-Group n ,
      right-inverse-law-add-fin-sequence-type-Group n)
```
