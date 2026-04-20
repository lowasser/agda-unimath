# Dependent products of real vector spaces

```agda
module linear-algebra.dependent-products-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.dependent-products-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

Given a type `I` and a family of
[real vector spaces](linear-algebra.real-vector-spaces.md) `Vᵢ` indexed by
`i : I`, the dependent product `Π (i : I) Vᵢ` is a real vector space.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  (V : I → ℝ-Vector-Space l2 l3)
  where

  Π-ℝ-Vector-Space : ℝ-Vector-Space l2 (l1 ⊔ l3)
  Π-ℝ-Vector-Space =
    Π-Vector-Space (heyting-field-ℝ l2) I V
```
