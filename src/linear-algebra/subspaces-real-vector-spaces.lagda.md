# Subspaces of real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.subspaces-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.subspaces-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

Given a [real vector space](linear-algebra.real-vector-spaces.md) `V` and a
[subset](linear-algebra.subsets-real-vector-spaces.md) `S ⊆ V` that contains
zero and is closed under addition and scalar multiplication, `S` is called a
{{#concept "subspace" Disambiguation="of a real vector space" Agda=subspace-ℝ-Vector-Space}}
of `V` and itself forms a real vector space.

## Definition

```agda
subspace-ℝ-Vector-Space :
  {l1 l2 : Level} (l3 : Level) → ℝ-Vector-Space l1 l2 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
subspace-ℝ-Vector-Space {l1} l3 =
  subspace-Vector-Space l3 (heyting-field-ℝ l1)

module _
  {l1 l2 l3 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (S : subspace-ℝ-Vector-Space l3 V)
  where

  vector-space-subspace-ℝ-Vector-Space : ℝ-Vector-Space l1 (l2 ⊔ l3)
  vector-space-subspace-ℝ-Vector-Space =
    vector-space-subspace-Vector-Space (heyting-field-ℝ l1) V S
```
