# Nonzero roots of positive real numbers

```agda
module real-numbers.nonzero-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-of-two

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-nonnegative-real-numbers
open import real-numbers.powers-positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.square-roots-positive-real-numbers
```

</details>

## Idea

For [nonzero](elementary-number-theory.nonzero-natural-numbers.md) `n`, the
{{#concept "nth root" Disambiguation="of a positive real number" Agda=root-nonzero-nat-ℝ⁺}}
is the inverse operation to the `n`th
[power](real-numbers.powers-positive-real-numbers.md) operation on the
[positive real numbers](real-numbers.positive-real-numbers.md).

## Definition

```agda
real-root-pair-expansion-ℝ⁺ : {l : Level} → ℕ → ℕ → ℝ⁺ l → ℝ l
real-root-pair-expansion-ℝ⁺ u v x =
  real-root-pair-expansion-ℝ⁰⁺ u v (nonnegative-ℝ⁺ x)

real-root-nonzero-nat-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ l
real-root-nonzero-nat-ℝ⁺ n x =
  real-ℝ⁰⁺ (root-nonzero-nat-ℝ⁰⁺ n (nonnegative-ℝ⁺ x))

abstract opaque
  unfolding root-pair-expansion-ℝ⁰⁺

  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁺ l) →
    is-positive-ℝ (real-root-pair-expansion-ℝ⁺ u v x)
  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ zero-ℕ v x =
    is-positive-root-is-odd-exponent-real-ℝ⁺
      ( succ-ℕ (v *ℕ 2))
      ( is-odd-has-odd-expansion _ (v , refl))
      ( x)
  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ (succ-ℕ u) v x =
    tr
      ( is-positive-ℝ ∘ real-root-pair-expansion-ℝ⁰⁺ u v)
      ( eq-ℝ⁰⁺ _ _ refl)
      ( is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ u v (sqrt-ℝ⁺ x))

  is-positive-real-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    is-positive-ℝ (real-root-nonzero-nat-ℝ⁺ n x)
  is-positive-real-root-nonzero-nat-ℝ⁺ (0 , H) = ex-falso (H refl)
  is-positive-real-root-nonzero-nat-ℝ⁺ (succ-ℕ n , _) x =
    let ((u , v) , _) = has-pair-expansion n in
    is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ u v x

root-nonzero-nat-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ⁺ l
root-nonzero-nat-ℝ⁺ n x =
  ( real-root-nonzero-nat-ℝ⁺ n x ,
    is-positive-real-root-nonzero-nat-ℝ⁺ n x)
```

## Properties

### The root operation is the inverse of the power operation

```agda
abstract
  is-section-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    power-ℝ⁺ (nat-ℕ⁺ n) (root-nonzero-nat-ℝ⁺ n x) ＝ x
  is-section-root-nonzero-nat-ℝ⁺ n⁺@(n , _) x =
    eq-ℝ⁺ _ _
      ( equational-reasoning
        real-ℝ⁺ (power-ℝ⁺ n (root-nonzero-nat-ℝ⁺ n⁺ x))
        ＝ power-ℝ n (real-root-nonzero-nat-ℝ⁺ n⁺ x)
          by real-power-ℝ⁺ n _
        ＝ real-ℝ⁰⁺ (power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))
          by inv (real-power-ℝ⁰⁺ n _)
        ＝ real-ℝ⁺ x
          by
            ap real-ℝ⁰⁺ (is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))

  is-retraction-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    root-nonzero-nat-ℝ⁺ n (power-ℝ⁺ (nat-ℕ⁺ n) x) ＝ x
  is-retraction-root-nonzero-nat-ℝ⁺ n⁺@(n , _) x =
    eq-ℝ⁺ _ _
      ( equational-reasoning
        real-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ (power-ℝ⁺ n x))
        ＝ real-root-nonzero-nat-ℝ⁰⁺ n⁺ (power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x))
          by
            ap
              ( real-root-nonzero-nat-ℝ⁰⁺ n⁺)
              ( eq-ℝ⁰⁺ _ _
                ( ( real-power-ℝ⁺ n x) ∙
                  ( inv (real-power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x)))))
        ＝ real-ℝ⁺ x
          by
            ap
              ( real-ℝ⁰⁺)
              ( is-retraction-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))

is-equiv-power-nonzero-nat-ℝ⁺ :
  {l : Level} (n : ℕ⁺) → is-equiv (power-ℝ⁺ {l} (nat-ℕ⁺ n))
is-equiv-power-nonzero-nat-ℝ⁺ n =
  is-equiv-is-invertible
    ( root-nonzero-nat-ℝ⁺ n)
    ( is-section-root-nonzero-nat-ℝ⁺ n)
    ( is-retraction-root-nonzero-nat-ℝ⁺ n)

aut-power-nonzero-nat-ℝ⁺ :
  {l : Level} (n : ℕ⁺) → Aut (ℝ⁺ l)
aut-power-nonzero-nat-ℝ⁺ n =
  ( power-ℝ⁺ (nat-ℕ⁺ n) ,
    is-equiv-power-nonzero-nat-ℝ⁺ n)
```
