# Indicator finite sequences in rings

```agda
module linear-algebra.indicator-finite-sequences-in-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.universe-levels

open import linear-algebra.dot-product-finite-sequences-in-rings
open import linear-algebra.finite-sequences-in-rings

open import ring-theory.rings

open import univalent-combinatorics.equality-standard-finite-types
```

</details>

## Idea

The
{{#concept "indicator finite sequence" Disambiguation="in a ring" Agda=indicator-fin-sequence-type-Ring}}
in a ring `R` `χᵢ` for index `i : Fin n` is a
[finite sequence](linear-algebra.finite-sequences-in-rings.md) in `R` `u` such
that `uᵢ = 1` and `uⱼ = 0` whenever `j ≠ i`.

## Definition

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

## Properties

### The dot product of an indicator sequence for index `i` with a finite sequence `v` is `v i`

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
