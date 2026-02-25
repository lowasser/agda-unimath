# The internal direct sum of families of subgroups of abelian groups

```agda
module group-theory.internal-direct-sum-subgroups-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.subgroups-abelian-groups
open import group-theory.subsets-abelian-groups
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "internal direct sum" Disambiguation="of a family of subgroups of an abelian group" Agda=direct-sum-family-Subgroup-Ab}}
of a family of [subgroups](group-theory.subgroups-abelian-groups.md) `Hᵢ` of an
[abelian group](group-theory.abelian-groups.md) `G`, indexed by `i : I`, is the
subgroup of `G` consisting of elements that can be expressed as
[finite sums](group-theory.sums-of-finite-sequences-of-elements-abelian-groups.md)
of elements of the `Hᵢ`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (G : Ab l1)
  (I : UU l2)
  (H : I → Subgroup-Ab l3 G)
  where

  subtype-direct-sum-family-Subgroup-Ab :
    subset-Ab (l1 ⊔ l2 ⊔ l3) G
  subtype-direct-sum-family-Subgroup-Ab x =
    ∃ ( Σ ℕ (fin-sequence (Σ I (type-Subgroup-Ab G ∘ H))))
      ( λ (n , seq) →
        Id-Prop
          ( set-Ab G)
          ( sum-fin-sequence-type-Ab G n (pr1 ∘ pr2 ∘ seq))
          ( x))

  abstract
    contains-zero-subtype-direct-sum-family-Subgroup-Ab :
      is-in-subtype
        ( subtype-direct-sum-family-Subgroup-Ab)
        ( zero-Ab G)
    contains-zero-subtype-direct-sum-family-Subgroup-Ab =
      intro-exists (0 , λ ()) refl

    is-closed-under-addition-subtype-direct-sum-family-Subgroup-Ab :
      is-closed-under-addition-subset-Ab
        ( G)
        ( subtype-direct-sum-family-Subgroup-Ab)
    is-closed-under-addition-subtype-direct-sum-family-Subgroup-Ab {a} {b} =
      map-binary-trunc-Prop
        ( λ ((na , fa) , ∑fa=a) ((nb , fb) , ∑fb=b) →
          let
            fab i =
              rec-coproduct
                ( fa)
                ( fb)
                ( map-inv-compute-coproduct-Fin na nb i)
          in
            ( ( na +ℕ nb , fab) ,
              ( equational-reasoning
                sum-fin-sequence-type-Ab G (na +ℕ nb) (pr1 ∘ pr2 ∘ fab)
                ＝
                  add-Ab G
                    ( sum-fin-sequence-type-Ab G
                      ( na)
                      ( pr1 ∘ pr2 ∘ fab ∘ inl-coproduct-Fin na nb))
                    ( sum-fin-sequence-type-Ab G
                      ( nb)
                      ( pr1 ∘ pr2 ∘ fab ∘ inr-coproduct-Fin na nb))
                  by
                    split-sum-fin-sequence-type-Ab G na nb (pr1 ∘ pr2 ∘ fab)
                ＝
                  add-Ab G
                    ( sum-fin-sequence-type-Ab G na (pr1 ∘ pr2 ∘ fa))
                    ( sum-fin-sequence-type-Ab G nb (pr1 ∘ pr2 ∘ fb))
                  by
                    ap-add-Ab G
                      ( htpy-sum-fin-sequence-type-Ab G
                        ( na)
                        ( λ i →
                          ap
                            ( pr1 ∘ pr2 ∘ rec-coproduct fa fb)
                            ( is-retraction-map-inv-equiv
                              ( compute-coproduct-Fin na nb)
                              ( inl i))))
                      ( htpy-sum-fin-sequence-type-Ab G
                        ( nb)
                        ( λ i →
                          ap
                            ( pr1 ∘ pr2 ∘ rec-coproduct fa fb)
                            ( is-retraction-map-inv-equiv
                              ( compute-coproduct-Fin na nb)
                              ( inr i))))
                ＝ add-Ab G a b
                  by ap-add-Ab G ∑fa=a ∑fb=b)))

    is-closed-under-negatives-subtype-direct-sum-family-Subgroup-Ab :
      is-closed-under-negatives-subset-Ab
        ( G)
        ( subtype-direct-sum-family-Subgroup-Ab)
    is-closed-under-negatives-subtype-direct-sum-family-Subgroup-Ab {x} =
      map-trunc-Prop
        ( λ ((n , f) , ∑f=x) →
          ( ( n ,
              ( tot
                ( λ i (gᵢ , gᵢ∈Hᵢ) →
                  ( neg-Ab G gᵢ ,
                    is-closed-under-negatives-Subgroup-Ab G (H i) gᵢ∈Hᵢ))) ∘
              ( f)) ,
            ( ( inv (distributive-neg-sum-fin-sequence-type-Ab G n _)) ∙
              ( ap (neg-Ab G) ∑f=x))))

  direct-sum-family-Subgroup-Ab : Subgroup-Ab (l1 ⊔ l2 ⊔ l3) G
  direct-sum-family-Subgroup-Ab =
    ( subtype-direct-sum-family-Subgroup-Ab ,
      contains-zero-subtype-direct-sum-family-Subgroup-Ab ,
      is-closed-under-addition-subtype-direct-sum-family-Subgroup-Ab ,
      is-closed-under-negatives-subtype-direct-sum-family-Subgroup-Ab)

  abstract
    leq-direct-sum-family-Subgroup-Ab :
      (i : I) →
      leq-Subgroup-Ab
        ( G)
        ( H i)
        ( direct-sum-family-Subgroup-Ab)
    leq-direct-sum-family-Subgroup-Ab i h h∈Hᵢ =
      intro-exists
        ( 1 , λ _ → (i , (h , h∈Hᵢ)))
        ( compute-sum-one-element-Ab G (λ _ → h))
```
