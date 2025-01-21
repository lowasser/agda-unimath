# The monoid of rational numbers with addition

```agda
module elementary-number-theory.monoid-of-rational-numbers-with-addition where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The rational numbers equipped with `0` and addition is a commutative monoid.

## Definitions

### The Semigroup of rational numbers

```agda
ℚ-Semigroup : Semigroup lzero
pr1 ℚ-Semigroup = ℚ-Set
pr1 (pr2 ℚ-Semigroup) = add-ℚ
pr2 (pr2 ℚ-Semigroup) = associative-add-ℚ
```

### The monoid of rational numbers

```agda
ℚ-Monoid : Monoid lzero
pr1 ℚ-Monoid = ℚ-Semigroup
pr1 (pr2 ℚ-Monoid) = zero-ℚ
pr1 (pr2 (pr2 ℚ-Monoid)) = left-unit-law-add-ℚ
pr2 (pr2 (pr2 ℚ-Monoid)) = right-unit-law-add-ℚ
```

### The commutative monoid of rational numbers

```agda
ℚ-Commutative-Monoid : Commutative-Monoid lzero
pr1 ℚ-Commutative-Monoid = ℚ-Monoid
pr2 ℚ-Commutative-Monoid = commutative-add-ℚ
```
