# Subsequences

```agda
module lists.subsequences where
```

<details><summary>Imports</summary>

```agda
open import order-theory.order-preserving-maps-posets
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.coproduct-types

open import lists.sequences

open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
```

</details>

## Idea

A {{concept "subsequence" WD="subsequence" WDID=Q1332977 Agda=subsequence}} of a
[sequence](lists.sequences.md) `u : ℕ → A` is a sequence `u ∘ f` for some
[strictly increasing](order-theory.strict-order-preserving-maps.md) sequence
`f : ℕ → ℕ`.

## Definitions

### Subsequences of a sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence =
    hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  extract-subsequence : subsequence → ℕ → ℕ
  extract-subsequence =
    map-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  is-strictly-increasing-extract-subsequence :
    (f : subsequence) →
    preserves-strict-order-map-Strictly-Preordered-Set
      ( strictly-preordered-set-ℕ)
      ( strictly-preordered-set-ℕ)
      ( extract-subsequence f)
  is-strictly-increasing-extract-subsequence =
    preserves-strict-order-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  abstract
    is-increasing-extract-subsequence :
      (f : subsequence) →
      preserves-order-Poset
        ( ℕ-Poset)
        ( ℕ-Poset)
        ( extract-subsequence f)
    is-increasing-extract-subsequence (f , H) a b a≤b =
      rec-coproduct
        ( λ a=b → leq-eq-ℕ (f a) (f b) (ap f a=b))
        ( λ a<b → leq-le-ℕ (f a) (f b) (H a b a<b))
        ( eq-or-le-leq-ℕ a b a≤b)

  seq-subsequence : subsequence → sequence A
  seq-subsequence f n = u (extract-subsequence f n)
```

## Properties

### Any sequence is a subsequence of itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-subsequence : subsequence u
  refl-subsequence = id-hom-Strictly-Preordered-Set strictly-preordered-set-ℕ
```

### A subsequence of a subsequence is a subsequence of the original sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  sub-subsequence :
    (v : subsequence u) →
    (w : subsequence (seq-subsequence u v)) →
    subsequence u
  sub-subsequence =
    comp-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ
```

### The extraction sequence of a subsequence is superlinear

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  abstract
    is-superlinear-extract-subsequence :
      (n : ℕ) → leq-ℕ n (extract-subsequence u v n)
    is-superlinear-extract-subsequence zero-ℕ =
      leq-zero-ℕ (extract-subsequence u v zero-ℕ)
    is-superlinear-extract-subsequence (succ-ℕ n) =
      leq-succ-le-ℕ
        ( n)
        ( extract-subsequence u v (succ-ℕ n))
        ( concatenate-leq-le-ℕ
          { n}
          { extract-subsequence u v n}
          { extract-subsequence u v (succ-ℕ n)}
          ( is-superlinear-extract-subsequence n)
          ( le-succ-is-strictly-increasing-sequence-Strictly-Preordered-Set
            ( strictly-preordered-set-ℕ)
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( n)))
```

### The subsequence of dropping leading elements

```agda
module _
  {l : Level} {A : UU l} (k : ℕ) (u : sequence A)
  where

  drop-subsequence : subsequence u
  drop-subsequence = (add-ℕ' k , preserves-le-right-add-ℕ k)
```

### The subsequence of taking every `k`th element for nonzero `k`

```agda
module _
  {l : Level} {A : UU l} (k : ℕ⁺) (u : sequence A)
  where

  mul-ℕ⁺-subsequence : subsequence u
  mul-ℕ⁺-subsequence =
    ( mul-ℕ' (nat-ℕ⁺ k) , preserves-le-right-mul-nat-ℕ⁺ k)

  seq-mul-ℕ⁺-subsequence : sequence A
  seq-mul-ℕ⁺-subsequence = seq-subsequence u mul-ℕ⁺-subsequence
```
