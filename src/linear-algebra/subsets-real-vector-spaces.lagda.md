# Subsets of real vector spaces

```agda
module linear-algebra.subsets-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.subsets-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a vector space" Agda=subset-Vector-Space}}
of a [real vector space](linear-algebra.real-vector-spaces.md) `V` is a
[subset](foundation.subtypes.md) of the underlying type of `V`.

## Definition

```agda
subset-ℝ-Vector-Space :
  {l1 l2 : Level} (l3 : Level) → ℝ-Vector-Space l1 l2 → UU (l2 ⊔ lsuc l3)
subset-ℝ-Vector-Space l3 V = subtype l3 (type-ℝ-Vector-Space V)
```

## Properties

### The proposition that a subset contains zero

```agda
module _
  {l1 l2 l3 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  contains-zero-prop-subset-ℝ-Vector-Space :
    subtype l3 (subset-ℝ-Vector-Space l3 V)
  contains-zero-prop-subset-ℝ-Vector-Space =
    contains-zero-prop-subset-Vector-Space (heyting-field-ℝ l1) V

  contains-zero-subset-ℝ-Vector-Space :
    subset-ℝ-Vector-Space l3 V → UU l3
  contains-zero-subset-ℝ-Vector-Space =
    is-in-subtype contains-zero-prop-subset-ℝ-Vector-Space
```

### The proposition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  is-closed-under-addition-prop-subset-ℝ-Vector-Space :
    subtype (l2 ⊔ l3) (subset-ℝ-Vector-Space l3 V)
  is-closed-under-addition-prop-subset-ℝ-Vector-Space =
    is-closed-under-addition-prop-subset-Vector-Space (heyting-field-ℝ l1) V

  is-closed-under-addition-subset-ℝ-Vector-Space :
    subset-ℝ-Vector-Space l3 V → UU (l2 ⊔ l3)
  is-closed-under-addition-subset-ℝ-Vector-Space =
    is-in-subtype is-closed-under-addition-prop-subset-ℝ-Vector-Space
```

### The proposition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  is-closed-under-scalar-multiplication-prop-subset-ℝ-Vector-Space :
    subtype (lsuc l1 ⊔ l2 ⊔ l3) (subset-ℝ-Vector-Space l3 V)
  is-closed-under-scalar-multiplication-prop-subset-ℝ-Vector-Space =
    is-closed-under-scalar-multiplication-prop-subset-Vector-Space
      ( heyting-field-ℝ l1)
      ( V)

  is-closed-under-scalar-multiplication-subset-ℝ-Vector-Space :
    subset-ℝ-Vector-Space l3 V → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-ℝ-Vector-Space =
    is-in-subtype
      ( is-closed-under-scalar-multiplication-prop-subset-ℝ-Vector-Space)
```
