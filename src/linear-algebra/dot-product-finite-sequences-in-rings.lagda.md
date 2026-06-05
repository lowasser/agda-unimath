# The dot product of finite sequences in rings

```agda
module linear-algebra.dot-product-finite-sequences-in-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings

open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings
```

</details>

## Idea

## Definition

```agda
dot-product-fin-sequence-type-Ring :
  {l : Level} (R : Ring l) (n : ℕ) →
  fin-sequence-type-Ring R n → fin-sequence-type-Ring R n → type-Ring R
dot-product-fin-sequence-type-Ring R n u v =
  sum-fin-sequence-type-Ring R n (λ i → mul-Ring R (u i) (v i))
```
