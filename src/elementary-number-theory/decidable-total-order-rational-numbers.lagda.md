# The decidable total order of rational numbers

```agda
module elementary-number-theory.decidable-total-order-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-rational-numbers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-ℚ : is-total-Poset ℚ-Poset
is-total-leq-ℚ x y = unit-trunc-Prop (linear-leq-ℚ x y)

ℚ-Total-Order : Total-Order lzero lzero
pr1 ℚ-Total-Order = ℚ-Poset
pr2 ℚ-Total-Order = is-total-leq-ℚ

ℚ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℚ-Decidable-Total-Order = ℚ-Poset
pr1 (pr2 ℚ-Decidable-Total-Order) = is-total-leq-ℚ
pr2 (pr2 ℚ-Decidable-Total-Order) = is-decidable-leq-ℚ
```

## Properties

### Minimum and maximum operations for `ℚ`

```agda
min-ℚ : ℚ → ℚ → ℚ
min-ℚ = min-Decidable-Total-Order ℚ-Decidable-Total-Order

max-ℚ : ℚ → ℚ → ℚ
max-ℚ = max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `min-ℚ x y ≤ x`

```agda
leq-left-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ x
leq-left-min-ℚ = leq-left-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `min-ℚ x y ≤ y`

```agda
leq-right-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ y
leq-right-min-ℚ = leq-right-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `x ≤ max-ℚ x y`

```agda
leq-left-max-ℚ : (x y : ℚ) → x ≤-ℚ max-ℚ x y
leq-left-max-ℚ = leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `y ≤ max-ℚ x y`

```agda
leq-right-max-ℚ : (x y : ℚ) → y ≤-ℚ max-ℚ x y
leq-right-max-ℚ = leq-right-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `min-ℚ` is commutative

```agda
commutative-min-ℚ : (x y : ℚ) → min-ℚ x y ＝ min-ℚ y x
commutative-min-ℚ =
  commutative-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `max-ℚ` is commutative

```agda
commutative-max-ℚ : (x y : ℚ) → max-ℚ x y ＝ max-ℚ y x
commutative-max-ℚ =
  commutative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```
