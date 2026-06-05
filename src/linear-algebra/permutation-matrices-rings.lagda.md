# Permutation matrices on rings

```agda
module linear-algebra.permutation-matrices-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-types
open import elementary-number-theory.natural-numbers
open import foundation.equivalences
open import foundation.propositions
open import foundation.decidable-propositions
open import ring-theory.rings
open import foundation.identity-types
open import foundation.negation
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
open import foundation.binary-homotopies
open import foundation.universe-levels
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.identity-matrices-on-rings
open import linear-algebra.square-matrices-on-rings
open import linear-algebra.transposition-matrices
open import linear-algebra.multiplication-square-matrices-on-rings
```

</details>

## Idea

## Definition

```agda
permutation-matrix-Ring :
  {l : Level} (R : Ring l) (n : ℕ) → Permutation n → square-matrix-Ring R n
permutation-matrix-Ring R n σ i =
  indicator-fin-sequence-type-Ring R n (map-equiv σ i)
```

## Properties

### The permutation matrix of the identity permutation is the identity matrix

```agda
id-permutation-matrix-Ring :
  {l : Level} (R : Ring l) (n : ℕ) →
  permutation-matrix-Ring R n id-equiv ＝ id-matrix-Ring R n
id-permutation-matrix-Ring R n = refl
```

### The transpose of the matrix of a permutation `σ` is the matrix of the permutation `σ⁻¹`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (σ : Permutation n)
  where abstract

  binary-htpy-transpose-permutation-matrix-Ring :
    binary-htpy
      ( transpose-square-matrix n (permutation-matrix-Ring R n σ))
      ( permutation-matrix-Ring R n (inv-equiv σ))
  binary-htpy-transpose-permutation-matrix-Ring i j =
    let
      is-prop-is-decidable-σj=i =
        is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i)
      is-prop-is-decidable-σ⁻¹i=j =
        is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j)
      σj=i⇒σ⁻¹i=j σj=i =
        ap (map-inv-equiv σ) (inv σj=i) ∙ is-retraction-map-inv-equiv σ j
    in
      rec-coproduct
        ( λ σj=i →
          equational-reasoning
            rec-coproduct
              ( λ _ → one-Ring R)
              ( λ _ → zero-Ring R)
              ( has-decidable-equality-Fin n (map-equiv σ j) i)
            ＝ one-Ring R
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i))
                    ( has-decidable-equality-Fin n (map-equiv σ j) i)
                    ( inl σj=i))
            ＝
              rec-coproduct
                ( λ _ → one-Ring R)
                ( λ _ → zero-Ring R)
                ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j))
                    ( inl (σj=i⇒σ⁻¹i=j σj=i))
                    ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)))
        ( λ σj≠i →
          equational-reasoning
            rec-coproduct
              ( λ _ → one-Ring R)
              ( λ _ → zero-Ring R)
              ( has-decidable-equality-Fin n (map-equiv σ j) i)
            ＝ zero-Ring R
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i))
                    ( has-decidable-equality-Fin n (map-equiv σ j) i)
                    ( inr σj≠i))
            ＝
              rec-coproduct
                ( λ _ → one-Ring R)
                ( λ _ → zero-Ring R)
                ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j))
                    ( inr (map-neg (eq-map-equiv-eq-map-inv-equiv σ j i) σj≠i))
                    ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)))
        ( has-decidable-equality-Fin n (map-equiv σ j) i)

  transpose-permutation-matrix-Ring :
    transpose-square-matrix n (permutation-matrix-Ring R n σ) ＝
    permutation-matrix-Ring R n (inv-equiv σ)
  transpose-permutation-matrix-Ring =
    eq-binary-htpy _ _ binary-htpy-transpose-permutation-matrix-Ring
```

### Multiplication by a permutation matrix permutes the rows of a matrix

```agda
left-mul-permutation-matrix-Ring :
  ?
```
