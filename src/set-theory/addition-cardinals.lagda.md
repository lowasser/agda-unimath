# Addition of cardinalities of sets

```agda
module set-theory.addition-cardinals where
```

<details><summary>Imports</summary>

```agda
open import set-theory.cardinalities
open import foundation.dependent-pair-types
-- open import commutative-algebra.commutative-semirings
open import foundation.set-truncations
open import foundation.action-on-identifications-functions
-- open import group-theory.semigroups
open import foundation.propositional-truncations
-- open import group-theory.monoids
open import foundation.coproduct-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.truncated-types
open import foundation.identity-types
open import group-theory.commutative-monoids
open import foundation.sets
open import foundation.equality-coproduct-types
open import foundation.universe-levels
open import foundation.truncation-levels
open import foundation.truncations
```

</details>

## Idea

## Definition

```agda
add-cardinal : {l1 l2 : Level} → cardinal l1 → cardinal l2 → cardinal (l1 ⊔ l2)
add-cardinal {l1} {l2} |X| |Y| =
  let open do-syntax-trunc (trunc-Set (Set (l1 ⊔ l2)))
  in do
    X ← |X|
    Y ← |Y|
    cardinality (coproduct-Set X Y)
```

## Properties

### Addition on cardinalities agrees with the coproducts of sets

```agda
eq-add-cardinal-coproduct-Set :
  {l1 l2 : Level} → (A : Set l1) (B : Set l2) →
  add-cardinal (cardinality A) (cardinality B) ＝
  cardinality (coproduct-Set A B)
eq-add-cardinal-coproduct-Set A B =
  {! triangle-universal-property-trunc ? ? ?  !}
```

### Associativity

```agda
associative-add-cardinal :
  {l1 l2 l3 : Level} → (x : cardinal l1) (y : cardinal l2) (z : cardinal l3) →
  add-cardinal (add-cardinal x y) z ＝ add-cardinal x (add-cardinal y z)
associative-add-cardinal |X| |Y| |Z| =
  let
    open do-syntax-trunc ({!  add-cardinal (add-cardinalx y) z !} ＝ {!   !} , {! is-trunc-succ-is-trunc ? ? ? ?  !})
  in do
    X ← |X|
    Y ← |Y|
    Z ← |Z|
    let
      H = eq-mere-equiv-cardinality (coproduct-Set (coproduct-Set X Y) Z) (coproduct-Set X (coproduct-Set Y Z)) (unit-trunc-Prop associative-coproduct)
    {!  !}
```
