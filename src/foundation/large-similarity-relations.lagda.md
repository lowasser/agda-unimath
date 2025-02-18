# Large similarity relations

```agda
module foundation.large-similarity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

A {{#concept "large similarity relation" Agda=Large-Similarity-Relation}} on a
family of types indexed by universe levels `A` is a
[large preorder](order-theory.large-preorders.md) `R` (a
[large binary relation](foundation.large-binary-relations.md) which is reflexive
and transitive) that satisfies the following properties:

- **Symmetry:** if `R a b`, then `R b a`.
- **Coincides with equality:** if `a` and `b` are at the same universe level and
  `R a b`, then `a ＝ b`.

```agda
record Large-Similarity-Relation
  (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Similarity-Relation
  field
    large-preorder-Large-Similarity-Relation :
      Large-Preorder α β

  type-Large-Similarity-Relation : (l : Level) → UU (α l)
  type-Large-Similarity-Relation =
    type-Large-Preorder large-preorder-Large-Similarity-Relation

  sim-prop-Large-Similarity-Relation :
    Large-Relation-Prop β type-Large-Similarity-Relation
  sim-prop-Large-Similarity-Relation =
    leq-prop-Large-Preorder large-preorder-Large-Similarity-Relation

  sim-Large-Similarity-Relation :
    {l1 l2 : Level} →
    (a : type-Large-Similarity-Relation l1)
    (b : type-Large-Similarity-Relation l2) →
    UU (β l1 l2)
  sim-Large-Similarity-Relation a b =
    type-Prop (sim-prop-Large-Similarity-Relation a b)

  field
    symmetric-sim-Large-Similarity-Relation :
      is-symmetric-Large-Relation-Prop
        ( type-Large-Similarity-Relation)
        ( sim-prop-Large-Similarity-Relation)
    eq-sim-Large-Similarity-Relation :
      {l : Level} → (a b : type-Large-Similarity-Relation l) →
      sim-Large-Similarity-Relation a b → a ＝ b
```
