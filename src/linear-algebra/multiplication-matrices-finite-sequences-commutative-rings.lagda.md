# Multiplying matrices and finite sequences on commutative rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.multiplication-matrices-finite-sequences-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.column-matrices
open import linear-algebra.column-matrices-on-commutative-rings
open import linear-algebra.finite-sequences-in-commutative-rings
open import linear-algebra.function-left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.matrices-on-commutative-rings
open import linear-algebra.multiplication-matrices-finite-sequences-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The product of an `m × n`
[matrix](linear-algebra.matrices-on-commutative-rings.md) on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` and a
[finite sequence](linear-algebra.finite-sequences-in-commutative-rings.md) `v`
of length `n` in `R` is the `m`-element finite sequence `w` defined as
`wᵢ ≔ ∑ⱼ Mᵢⱼ vⱼ`.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  where

  mul-matrix-fin-sequence-type-Commutative-Ring :
    matrix-Commutative-Ring R m n →
    fin-sequence-type-Commutative-Ring R n →
    fin-sequence-type-Commutative-Ring R m
  mul-matrix-fin-sequence-type-Commutative-Ring =
    mul-matrix-fin-sequence-type-Ring (ring-Commutative-Ring R) m n
```

### Multiplication by a matrix is a linear map

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  (M : matrix-Commutative-Ring R m n)
  (let _+R_ = add-Commutative-Ring R)
  (let _*R_ = mul-Commutative-Ring R)
  where abstract

  is-additive-mul-matrix-fin-sequence-type-Commutative-Ring :
    is-additive-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-type-Commutative-Ring R n)
      ( left-module-fin-sequence-type-Commutative-Ring R m)
      ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
  is-additive-mul-matrix-fin-sequence-type-Commutative-Ring u v =
    eq-htpy
      ( λ i →
        ( htpy-sum-fin-sequence-type-Commutative-Ring R n
          ( λ j →
            left-distributive-mul-add-Commutative-Ring
              ( R)
              ( M i j)
              ( u j)
              ( v j))) ∙
        ( inv (interchange-add-sum-fin-sequence-type-Commutative-Ring R n _ _)))

  is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring :
    is-homogeneous-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-type-Commutative-Ring R n)
      ( left-module-fin-sequence-type-Commutative-Ring R m)
      ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
  is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring c v =
    eq-htpy
      ( λ i →
        ( htpy-sum-fin-sequence-type-Commutative-Ring R n
          ( λ j → left-swap-mul-Commutative-Ring R (M i j) c (v j))) ∙
        ( inv
          ( left-distributive-mul-sum-fin-sequence-type-Commutative-Ring
            ( R)
            ( n)
            ( c)
            ( _))))

  is-linear-mul-matrix-fin-sequence-type-Commutative-Ring :
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-type-Commutative-Ring R n)
      ( left-module-fin-sequence-type-Commutative-Ring R m)
      ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
  is-linear-mul-matrix-fin-sequence-type-Commutative-Ring =
    ( is-additive-mul-matrix-fin-sequence-type-Commutative-Ring ,
      is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring)
```
