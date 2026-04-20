# Subsets of vector spaces

```agda
module linear-algebra.subsets-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.subsets-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a vector space" Agda=subset-Vector-Space}}
of a [vector space](linear-algebra.vector-spaces.md) `V` is a
[subset](foundation.subtypes.md) of the underlying type of `V`.

## Definitions

### Subsets of left modules over commutative rings

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  subset-Vector-Space : UU (l2 ⊔ lsuc l3)
  subset-Vector-Space =
    subtype l3 (type-Vector-Space K V)
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (S : subset-Vector-Space l3 K V)
  where

  is-closed-under-addition-prop-subset-Vector-Space :
    Prop (l2 ⊔ l3)
  is-closed-under-addition-prop-subset-Vector-Space =
    is-closed-under-addition-prop-subset-left-module-Ring
      ( ring-Heyting-Field K)
      ( V)
      ( S)

  is-closed-under-addition-subset-Vector-Space : UU (l2 ⊔ l3)
  is-closed-under-addition-subset-Vector-Space =
    type-Prop is-closed-under-addition-prop-subset-Vector-Space
```

### The condition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (S : subset-Vector-Space l3 K V)
  where

  is-closed-under-scalar-multiplication-prop-subset-Vector-Space :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-prop-subset-Vector-Space =
    is-closed-under-scalar-multiplication-prop-subset-left-module-Ring
      ( ring-Heyting-Field K)
      ( V)
      ( S)

  is-closed-under-scalar-multiplication-subset-Vector-Space :
    UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-Vector-Space =
    type-Prop
      ( is-closed-under-scalar-multiplication-prop-subset-Vector-Space)
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (S : subset-Vector-Space l3 K V)
  where

  contains-zero-prop-subset-Vector-Space : Prop l3
  contains-zero-prop-subset-Vector-Space =
    contains-zero-prop-subset-left-module-Ring
      ( ring-Heyting-Field K)
      ( V)
      ( S)

  contains-zero-subset-Vector-Space : UU l3
  contains-zero-subset-Vector-Space =
    type-Prop contains-zero-prop-subset-Vector-Space
```
