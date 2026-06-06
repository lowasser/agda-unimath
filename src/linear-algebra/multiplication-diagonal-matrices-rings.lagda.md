# Multiplication by diagonal matrices over rings

```agda
module linear-algebra.multiplication-diagonal-matrices-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import linear-algebra.diagonal-matrices-on-rings
open import univalent-combinatorics.standard-finite-types
open import foundation.identity-types
open import linear-algebra.multiplication-matrices-on-rings
open import foundation.binary-homotopies
open import linear-algebra.matrices-on-rings
open import linear-algebra.finite-sequences-in-rings
open import ring-theory.rings
open import foundation.universe-levels
```

</details>

## Idea

## Properties

### Left multiplication by a diagonal matrix with diagonal `d` multiplies row `i` by `dᵢ`

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  (d : fin-sequence-type-Ring R m)
  where abstract

  compute-left-mul-diagonal-matrix-Ring :
    (M : matrix-Ring R m n) (i : Fin m) (j : Fin n) →
    mul-matrix-Ring R m m n
      ( matrix-from-diagonal-fin-sequence-type-Ring R m d)
      ( M)
      ( i)
      ( j) ＝
    mul-Ring R (d i) (M i j)
  compute-left-mul-diagonal-matrix-Ring M i j =
    equational-reasoning
      {!   !} ＝ {!   !} by {!   !}

```
