# The free group on a set of generators

```agda
module group-theory.free-groups-on-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.sets
open import foundation.existential-quantification
open import foundation.equivalence-relations
open import foundation.subtypes
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.binary-functoriality-set-quotients
open import foundation.equivalence-classes
open import foundation.set-quotients
open import foundation.disjunction
open import foundation.function-types
open import foundation.empty-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import group-theory.groups
open import foundation.unit-type
open import foundation.propositions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.equality-coproduct-types
open import lists.lists
open import foundation.binary-relations
```

</details>

## Idea

The {{#concept "free group" WD="free group" WDID=Q431078}} on a set `S`
is the [group](group-theory.groups.md) that TODO.

## Definition

### Realization of the free group on a set of generators

```agda
data base-free-group-Set {l : Level} (S : Set l) : UU l where
  unit-base-free-group-Set :
    base-free-group-Set S
  emb-base-free-group-Set :
    type-Set S → base-free-group-Set S
  mul-base-free-group-Set :
    base-free-group-Set S → base-free-group-Set S → base-free-group-Set S
  inv-base-free-group-Set :
    base-free-group-Set S → base-free-group-Set S

data Eq-base-free-group-Set {l : Level} (S : Set l) :
    Relation l (base-free-group-Set S) where
  refl-Eq-base-free-group-Set :
    (x : base-free-group-Set S) →
    Eq-base-free-group-Set S x x
  sym-Eq-base-free-group-Set :
    (x y : base-free-group-Set S) → Eq-base-free-group-Set S x y →
    Eq-base-free-group-Set S y x
  transitive-Eq-base-free-group-Set :
    (x y z : base-free-group-Set S) →
    Eq-base-free-group-Set S y z →
    Eq-base-free-group-Set S x y →
    Eq-base-free-group-Set S x z
  ap-left-mul-Eq-base-free-group-Set :
    (x y z : base-free-group-Set S) →
    Eq-base-free-group-Set S x y →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set x z)
      ( mul-base-free-group-Set y z)
  ap-right-mul-Eq-base-free-group-Set :
    (x y z : base-free-group-Set S) →
    Eq-base-free-group-Set S y z →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set x y)
      ( mul-base-free-group-Set x z)
  ap-inv-Eq-base-free-group-Set :
    (x y : base-free-group-Set S) →
    Eq-base-free-group-Set S x y →
    Eq-base-free-group-Set
      ( S)
      ( inv-base-free-group-Set x)
      ( inv-base-free-group-Set y)
  left-unit-law-base-free-group-Set :
    (x : base-free-group-Set S) →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set unit-base-free-group-Set x)
      ( x)
  right-unit-law-base-free-group-Set :
    (x : base-free-group-Set S) →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set x unit-base-free-group-Set)
      ( x)
  left-inverse-law-base-free-group-Set :
    (x : base-free-group-Set S) →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set (inv-base-free-group-Set x) x)
      ( unit-base-free-group-Set)
  right-inverse-law-base-free-group-Set :
    (x : base-free-group-Set S) →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set x (inv-base-free-group-Set x))
      ( unit-base-free-group-Set)
  associative-law-base-free-group-Set :
    (x y z : base-free-group-Set S) →
    Eq-base-free-group-Set
      ( S)
      ( mul-base-free-group-Set (mul-base-free-group-Set x y) z)
      ( mul-base-free-group-Set x (mul-base-free-group-Set y z))

module _
  {l : Level} (S : Set l)
  where

  relation-prop-base-free-group-Set : Relation-Prop l (base-free-group-Set S)
  relation-prop-base-free-group-Set x y =
    trunc-Prop (Eq-base-free-group-Set S x y)

  is-reflexive-relation-prop-base-free-group-Set :
    is-reflexive-Relation-Prop relation-prop-base-free-group-Set
  is-reflexive-relation-prop-base-free-group-Set =
    unit-trunc-Prop ∘ refl-Eq-base-free-group-Set

  is-symmetric-relation-prop-base-free-group-Set :
    is-symmetric-Relation-Prop relation-prop-base-free-group-Set
  is-symmetric-relation-prop-base-free-group-Set x y =
    rec-trunc-Prop
      ( relation-prop-base-free-group-Set y x)
      ( unit-trunc-Prop ∘ sym-Eq-base-free-group-Set x y)

  is-transitive-relation-prop-base-free-group-Set :
    is-transitive-Relation-Prop relation-prop-base-free-group-Set
  is-transitive-relation-prop-base-free-group-Set x y z H K =
    let
      open do-syntax-trunc-Prop (relation-prop-base-free-group-Set x z)
    in do
      y~z ← H
      x~y ← K
      unit-trunc-Prop (transitive-Eq-base-free-group-Set x y z y~z x~y)

  equivalence-relation-base-free-group-Set :
    equivalence-relation l (base-free-group-Set S)
  equivalence-relation-base-free-group-Set =
    ( relation-prop-base-free-group-Set ,
      is-reflexive-relation-prop-base-free-group-Set ,
      is-symmetric-relation-prop-base-free-group-Set ,
      is-transitive-relation-prop-base-free-group-Set)

  type-free-group-Set : UU (lsuc l)
  type-free-group-Set =
    equivalence-class
      equivalence-relation-base-free-group-Set

  set-free-group-Set : Set (lsuc l)
  set-free-group-Set = equivalence-class-Set equivalence-relation-base-free-group-Set

  mul-free-group-Set :
    type-free-group-Set → type-free-group-Set → type-free-group-Set
  mul-free-group-Set (xsub , x) (ysub , y) =
    ( λ z →
      ∃ ( type-subtype xsub)
        ( λ (x , _) →
          ∃ ( type-subtype ysub)
            ( λ (y , _) →
              relation-prop-base-free-group-Set
                (mul-base-free-group-Set x y)
                ( z)))) ,
    {!   !}

  is-associative-mul-free-group-Set :
    (x y z : type-free-group-Set) →
    mul-free-group-Set (mul-free-group-Set x y) z ＝
    mul-free-group-Set x (mul-free-group-Set y z)
  is-associative-mul-free-group-Set x y z = {!   !}
```
