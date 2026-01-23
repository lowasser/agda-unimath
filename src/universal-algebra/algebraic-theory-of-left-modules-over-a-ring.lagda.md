# The algebraic theory of left modules over a ring

```agda
module universal-algebra.algebraic-theory-of-left-modules-over-a-ring where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.left-modules-rings

open import lists.tuples

open import ring-theory.rings

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

For any [ring](ring-theory.rings.md) `R`, there is an
{{#concept "algebraic theory of left modules over the ring" Agda=algebraic-theory-left-module-Ring}}
`R`. The type of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[left modules](linear-algebra.left-modules-rings.md) over `R`.

## Definition

```agda
data left-module-ops {l : Level} (R : Ring l) : UU l where
  zero-left-module-op add-left-module-op neg-left-module-op : left-module-ops R
  mul-left-module-op : type-Ring R → left-module-ops R

left-module-ring-signature : {l : Level} (R : Ring l) → signature l
pr1 (left-module-ring-signature R) = left-module-ops R
pr2 (left-module-ring-signature R) zero-left-module-op = 0
pr2 (left-module-ring-signature R) add-left-module-op = 2
pr2 (left-module-ring-signature R) neg-left-module-op = 1
pr2 (left-module-ring-signature R) (mul-left-module-op r) = 1

data left-module-laws {l : Level} (R : Ring l) : UU l where
  associative-add-left-module-laws : left-module-laws R

  left-inverse-law-add-left-module-laws : left-module-laws R
  left-unit-law-add-left-module-laws : left-module-laws R
  commutative-add-left-module-laws : left-module-laws R
  -- right laws follow from commutativity of addition

  left-distributive-law-mul-add-left-module-laws :
    type-Ring R → left-module-laws R
  right-distributive-law-mul-add-left-module-laws :
    type-Ring R → type-Ring R → left-module-laws R
  associative-law-mul-left-module-laws :
    type-Ring R → type-Ring R → left-module-laws R
  left-unit-law-mul-left-module-laws : left-module-laws R

module _
  {l : Level}
  (R : Ring l)
  (let op = op-term)
  (let var = var-term)
  where

  algebraic-theory-left-module-Ring :
    Algebraic-Theory l (left-module-ring-signature R)
  pr1 algebraic-theory-left-module-Ring = left-module-laws R
  pr2 algebraic-theory-left-module-Ring associative-add-left-module-laws =
    ( op
        ( add-left-module-op)
        ( op
          ( add-left-module-op)
          ( var 0 ∷ var 1 ∷ empty-tuple) ∷ var 2 ∷ empty-tuple) ,
      op
        ( add-left-module-op)
        ( var 0 ∷
          op
            ( add-left-module-op)
            ( var 1 ∷ var 2 ∷ empty-tuple) ∷
          empty-tuple))
  pr2 algebraic-theory-left-module-Ring left-inverse-law-add-left-module-laws =
    ( op
        ( add-left-module-op)
        ( op neg-left-module-op (var 0 ∷ empty-tuple) ∷
          var 0 ∷
          empty-tuple) ,
      op zero-left-module-op empty-tuple)
  pr2 algebraic-theory-left-module-Ring left-unit-law-add-left-module-laws =
    ( op
        ( add-left-module-op)
        ( op zero-left-module-op empty-tuple ∷ var 0 ∷ empty-tuple) ,
      var 0)
  pr2 algebraic-theory-left-module-Ring commutative-add-left-module-laws =
    ( op
        ( add-left-module-op)
        ( var 0 ∷ var 1 ∷ empty-tuple) ,
      op
        ( add-left-module-op)
        ( var 1 ∷ var 0 ∷ empty-tuple))
  pr2 algebraic-theory-left-module-Ring
    ( left-distributive-law-mul-add-left-module-laws r) =
    ( op
        ( mul-left-module-op r)
        ( op
            ( add-left-module-op)
            ( var 0 ∷ var 1 ∷ empty-tuple) ∷
          empty-tuple) ,
      op
        ( add-left-module-op)
        ( op (mul-left-module-op r) (var 0 ∷ empty-tuple) ∷
          op (mul-left-module-op r) (var 1 ∷ empty-tuple) ∷
          empty-tuple))
  pr2 algebraic-theory-left-module-Ring
    ( right-distributive-law-mul-add-left-module-laws r s) =
    ( op (mul-left-module-op (add-Ring R r s)) (var 0 ∷ empty-tuple) ,
      op
        ( add-left-module-op)
        ( op (mul-left-module-op r) (var 0 ∷ empty-tuple) ∷
          op (mul-left-module-op s) (var 0 ∷ empty-tuple) ∷
          empty-tuple))
  pr2 algebraic-theory-left-module-Ring
    ( associative-law-mul-left-module-laws r s) =
    ( op (mul-left-module-op (mul-Ring R r s)) (var 0 ∷ empty-tuple) ,
      op
        ( mul-left-module-op r)
        ( op (mul-left-module-op s) (var 0 ∷ empty-tuple) ∷ empty-tuple))
  pr2 algebraic-theory-left-module-Ring left-unit-law-mul-left-module-laws =
    ( op (mul-left-module-op (one-Ring R)) (var 0 ∷ empty-tuple) ,
      var 0)

algebra-left-module-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
algebra-left-module-Ring l2 R =
  Algebra
    ( l2)
    ( left-module-ring-signature R)
    ( algebraic-theory-left-module-Ring R)
```

## Properties

### The left module over `R` associated with an algebras in the theory of left modules over a ring `R`

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (A@((A-Set , models-A) , satisfies-A) : algebra-left-module-Ring l2 R)
  where

  type-algebra-left-module-Ring : UU l2
  type-algebra-left-module-Ring = type-Set A-Set

  add-algebra-left-module-Ring :
    type-algebra-left-module-Ring → type-algebra-left-module-Ring →
    type-algebra-left-module-Ring
  add-algebra-left-module-Ring x y =
    models-A add-left-module-op (x ∷ y ∷ empty-tuple)

  associative-add-algebra-left-module-Ring :
    (x y z : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring (add-algebra-left-module-Ring x y) z ＝
    add-algebra-left-module-Ring x (add-algebra-left-module-Ring y z)
  associative-add-algebra-left-module-Ring x y z =
    satisfies-A
      ( associative-add-left-module-laws)
      ( λ { 0 → x ; 1 → y ; (succ-ℕ (succ-ℕ _)) → z})

  commutative-add-algebra-left-module-Ring :
    (x y : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring x y ＝ add-algebra-left-module-Ring y x
  commutative-add-algebra-left-module-Ring x y =
    satisfies-A
      ( commutative-add-left-module-laws)
      ( λ { 0 → x ; (succ-ℕ _) → y})

  zero-algebra-left-module-Ring : type-algebra-left-module-Ring
  zero-algebra-left-module-Ring = models-A zero-left-module-op empty-tuple

  left-unit-law-add-algebra-left-module-Ring :
    (x : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring zero-algebra-left-module-Ring x ＝ x
  left-unit-law-add-algebra-left-module-Ring x =
    satisfies-A left-unit-law-add-left-module-laws (λ _ → x)

  right-unit-law-add-algebra-left-module-Ring :
    (x : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring x zero-algebra-left-module-Ring ＝ x
  right-unit-law-add-algebra-left-module-Ring x =
    ( commutative-add-algebra-left-module-Ring _ _) ∙
    ( left-unit-law-add-algebra-left-module-Ring x)

  neg-algebra-left-module-Ring :
    type-algebra-left-module-Ring → type-algebra-left-module-Ring
  neg-algebra-left-module-Ring x =
    models-A neg-left-module-op (x ∷ empty-tuple)

  left-inverse-law-add-algebra-left-module-Ring :
    (x : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring (neg-algebra-left-module-Ring x) x ＝
    zero-algebra-left-module-Ring
  left-inverse-law-add-algebra-left-module-Ring x =
    satisfies-A left-inverse-law-add-left-module-laws (λ _ → x)

  right-inverse-law-add-algebra-left-module-Ring :
    (x : type-algebra-left-module-Ring) →
    add-algebra-left-module-Ring x (neg-algebra-left-module-Ring x) ＝
    zero-algebra-left-module-Ring
  right-inverse-law-add-algebra-left-module-Ring x =
    ( commutative-add-algebra-left-module-Ring _ _) ∙
    ( left-inverse-law-add-algebra-left-module-Ring x)

  mul-algebra-left-module-Ring :
    type-Ring R → type-algebra-left-module-Ring → type-algebra-left-module-Ring
  mul-algebra-left-module-Ring r x =
    models-A (mul-left-module-op r) (x ∷ empty-tuple)

  left-distributive-law-mul-add-algebra-left-module-Ring :
    (r : type-Ring R) (x y : type-algebra-left-module-Ring) →
    mul-algebra-left-module-Ring r (add-algebra-left-module-Ring x y) ＝
    add-algebra-left-module-Ring
      ( mul-algebra-left-module-Ring r x)
      ( mul-algebra-left-module-Ring r y)
  left-distributive-law-mul-add-algebra-left-module-Ring r x y =
    satisfies-A
      ( left-distributive-law-mul-add-left-module-laws r)
      ( λ { 0 → x ; (succ-ℕ _) → y})

  right-distributive-law-mul-add-algebra-left-module-Ring :
    (r s : type-Ring R) (x : type-algebra-left-module-Ring) →
    mul-algebra-left-module-Ring (add-Ring R r s) x ＝
    add-algebra-left-module-Ring
      ( mul-algebra-left-module-Ring r x)
      ( mul-algebra-left-module-Ring s x)
  right-distributive-law-mul-add-algebra-left-module-Ring r s x =
    satisfies-A
      ( right-distributive-law-mul-add-left-module-laws r s)
      ( λ _ → x)

  left-unit-law-mul-algebra-left-module-Ring :
    (x : type-algebra-left-module-Ring) →
    mul-algebra-left-module-Ring (one-Ring R) x ＝ x
  left-unit-law-mul-algebra-left-module-Ring x =
    satisfies-A
      ( left-unit-law-mul-left-module-laws)
      ( λ _ → x)

  associative-mul-algebra-left-module-Ring :
    (r s : type-Ring R) (x : type-algebra-left-module-Ring) →
    mul-algebra-left-module-Ring (mul-Ring R r s) x ＝
    mul-algebra-left-module-Ring r (mul-algebra-left-module-Ring s x)
  associative-mul-algebra-left-module-Ring r s x =
    satisfies-A
      ( associative-law-mul-left-module-laws r s)
      ( λ _ → x)

  semigroup-algebra-left-module-Ring : Semigroup l2
  semigroup-algebra-left-module-Ring =
    ( A-Set ,
      add-algebra-left-module-Ring ,
      associative-add-algebra-left-module-Ring)

  is-unital-semigroup-algebra-left-module-Ring :
    is-unital-Semigroup semigroup-algebra-left-module-Ring
  is-unital-semigroup-algebra-left-module-Ring =
    ( zero-algebra-left-module-Ring ,
      left-unit-law-add-algebra-left-module-Ring ,
      right-unit-law-add-algebra-left-module-Ring)

  group-algebra-left-module-Ring : Group l2
  group-algebra-left-module-Ring =
    ( semigroup-algebra-left-module-Ring ,
      is-unital-semigroup-algebra-left-module-Ring ,
      neg-algebra-left-module-Ring ,
      left-inverse-law-add-algebra-left-module-Ring ,
      right-inverse-law-add-algebra-left-module-Ring)

  ab-algebra-left-module-Ring : Ab l2
  ab-algebra-left-module-Ring =
    ( group-algebra-left-module-Ring ,
      commutative-add-algebra-left-module-Ring)

  left-module-algebra-left-module-Ring : left-module-Ring l2 R
  left-module-algebra-left-module-Ring =
    make-left-module-Ring
      ( R)
      ( ab-algebra-left-module-Ring)
      ( mul-algebra-left-module-Ring)
      ( left-distributive-law-mul-add-algebra-left-module-Ring)
      ( right-distributive-law-mul-add-algebra-left-module-Ring)
      ( left-unit-law-mul-algebra-left-module-Ring)
      ( associative-mul-algebra-left-module-Ring)
```

### The algebra in the theory of left modules over `R` associated with a left module over `R`

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  algebra-left-module-ring-left-module-Ring :
    algebra-left-module-Ring l2 R
  pr1 (pr1 algebra-left-module-ring-left-module-Ring) =
    set-left-module-Ring R M
  pr2 (pr1 algebra-left-module-ring-left-module-Ring)
    zero-left-module-op empty-tuple =
    zero-left-module-Ring R M
  pr2 (pr1 algebra-left-module-ring-left-module-Ring)
    ( add-left-module-op) (x ∷ y ∷ empty-tuple) =
    add-left-module-Ring R M x y
  pr2 (pr1 algebra-left-module-ring-left-module-Ring)
    ( neg-left-module-op) (x ∷ empty-tuple) =
    neg-left-module-Ring R M x
  pr2 (pr1 algebra-left-module-ring-left-module-Ring)
    ( mul-left-module-op r) (x ∷ empty-tuple) =
    mul-left-module-Ring R M r x
  pr2 algebra-left-module-ring-left-module-Ring
    associative-add-left-module-laws assign =
    associative-add-left-module-Ring R M (assign 0) (assign 1) (assign 2)
  pr2 algebra-left-module-ring-left-module-Ring
    left-unit-law-add-left-module-laws assign =
    left-unit-law-add-left-module-Ring R M (assign 0)
  pr2 algebra-left-module-ring-left-module-Ring
    left-inverse-law-add-left-module-laws assign =
    left-inverse-law-add-left-module-Ring R M (assign 0)
  pr2 algebra-left-module-ring-left-module-Ring
    commutative-add-left-module-laws assign =
    commutative-add-left-module-Ring R M (assign 0) (assign 1)
  pr2 algebra-left-module-ring-left-module-Ring
    ( left-distributive-law-mul-add-left-module-laws r) assign =
    left-distributive-mul-add-left-module-Ring R M r (assign 0) (assign 1)
  pr2 algebra-left-module-ring-left-module-Ring
    ( right-distributive-law-mul-add-left-module-laws r s) assign =
    right-distributive-mul-add-left-module-Ring R M r s (assign 0)
  pr2 algebra-left-module-ring-left-module-Ring
    ( associative-law-mul-left-module-laws r s) assign =
    associative-mul-left-module-Ring R M r s (assign 0)
  pr2 algebra-left-module-ring-left-module-Ring
    ( left-unit-law-mul-left-module-laws) assign =
    left-unit-law-mul-left-module-Ring R M (assign 0)
```
