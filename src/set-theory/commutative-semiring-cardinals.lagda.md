# The commutative semiring of cardinals

```agda
module set-theory.commutative-semiring-cardinals where
```

<details><summary>Imports</summary>

```agda
open import set-theory.cardinalities
open import commutative-algebra.commutative-semirings
open import group-theory.semigroups
open import group-theory.monoids
open import group-theory.commutative-monoids
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

## Definition

### Addition of cardinals

```agda
add-cardinal : {l1 l2 : Level} → cardinal l1 → cardinal l2 → cardinal (l1 ⊔ l2)
add-cardinal |X| |Y| = ?
```
