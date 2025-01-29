# Dedekind real numbers

```agda
module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The lower cut (upper cut) of the sum of two real numbers is the set of sums of
elements of their lower (upper) cuts.

```agda
add-subtypes-ℚ : {l : Level} → subtype l ℚ → subtype l ℚ → subtype l ℚ
add-subtypes-ℚ A B q =
  ∃ (ℚ × ℚ) (λ (a , b) → A a ∧ B b ∧ (Id-Prop ℚ-Set (a +ℚ b) q))

module _
  {l : Level} (x y : ℝ l)
  where

  lower-cut-add-ℝ : subtype l ℚ
  lower-cut-add-ℝ = add-subtypes-ℚ (lower-cut-ℝ x) (lower-cut-ℝ y)

  upper-cut-add-ℝ : subtype l ℚ
  upper-cut-add-ℝ = add-subtypes-ℚ (upper-cut-ℝ x) (upper-cut-ℝ y)

  abstract
    lower-cut-inhabited-add-ℝ : exists ℚ lower-cut-add-ℝ
    lower-cut-inhabited-add-ℝ =
      elim-exists
        (∃ ℚ lower-cut-add-ℝ)
        (λ p p-in-lower-x →
          elim-exists
            (∃ ℚ lower-cut-add-ℝ)
            (λ q q-in-lower-y →
              intro-exists (p +ℚ q)
                (intro-exists (p , q) (p-in-lower-x , q-in-lower-y , refl)))
            (is-inhabited-lower-cut-ℝ y))
        (is-inhabited-lower-cut-ℝ x)

    upper-cut-inhabited-add-ℝ : exists ℚ upper-cut-add-ℝ
    upper-cut-inhabited-add-ℝ =
      elim-exists
        (∃ ℚ upper-cut-add-ℝ)
        (λ p p-in-upper-x →
          elim-exists
            (∃ ℚ upper-cut-add-ℝ)
            (λ q q-in-upper-y →
              intro-exists (p +ℚ q)
                (intro-exists (p , q) (p-in-upper-x , q-in-upper-y , refl)))
            (is-inhabited-upper-cut-ℝ y)
          )
        (is-inhabited-upper-cut-ℝ x)

    is-rounded-lower-cut-add-ℝ :
      (a : ℚ) →
      is-in-subtype lower-cut-add-ℝ a ↔
      exists ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b))
    pr1 (is-rounded-lower-cut-add-ℝ a) in-add-lower =
      elim-exists
        (∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
        (λ (p , q) (p-in-lower-x , q-in-lower-y , p+q=a) →
          elim-exists
            (∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
            (λ p' (p<p' , p'-in-lower-x) →
              elim-exists
                (∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
                (λ q' (q<q' , q'-in-lower-y) →
                  intro-exists
                    (p' +ℚ q')
                    (transp-leq-sum a p p' q q' p+q=a p<p' q<q' ,
                      intro-exists
                        (p' , q')
                        (p'-in-lower-x , q'-in-lower-y , refl)))
                (forward-implication (is-rounded-lower-cut-ℝ y q) q-in-lower-y))
            (forward-implication (is-rounded-lower-cut-ℝ x p) p-in-lower-x))
        in-add-lower
      where
        transp-leq-sum : (a p p' q q' : ℚ) → p +ℚ q ＝ a → le-ℚ p p' → le-ℚ q q' → le-ℚ a (p' +ℚ q')
        transp-leq-sum a p p' q q' p+q=a p<p' q<q' =
          tr
            (λ r → le-ℚ r (p' +ℚ q'))
            p+q=a
            (preserves-le-add-ℚ {p} {p'} {q} {q'} p<p' q<q')
    pr2 (is-rounded-lower-cut-add-ℝ a) =
      elim-exists
        (lower-cut-add-ℝ a)
        (λ b (a<b , b-in-lower-add) →
          elim-exists
            (lower-cut-add-ℝ a)
            (λ (p , q) (p-in-lower-x , q-in-lower-y , p+q=b) →
              intro-exists
                ((p +ℚ (a -ℚ b) , q))
                (backward-implication
                    (is-rounded-lower-cut-ℝ x (p +ℚ (a -ℚ b)))
                    (intro-exists p (plus-neg-le-self-ℚ p (a -ℚ b) (translate-diff-zero-le-ℚ a b a<b) , p-in-lower-x)) ,
                  q-in-lower-y ,
                  (right-swap-add-Ab abelian-group-add-ℚ p (a -ℚ b) q ∙
                    ap (_+ℚ (a -ℚ b)) p+q=b ∙
                    left-swap-add-Ab abelian-group-add-ℚ b a (neg-ℚ b) ∙
                    ap (a +ℚ_) (right-inverse-law-add-ℚ b) ∙
                    right-unit-law-add-ℚ a)))
            b-in-lower-add)
      where plus-neg-le-self-ℚ : (s t : ℚ) → le-ℚ t zero-ℚ → le-ℚ (s +ℚ t) s
            plus-neg-le-self-ℚ s t t<0 =
              tr
                (le-ℚ (s +ℚ t))
                (right-unit-law-add-ℚ s)
                (preserves-le-right-add-ℚ s t zero-ℚ t<0)
            translate-diff-zero-le-ℚ : (s t : ℚ) → le-ℚ s t → le-ℚ (s -ℚ t) zero-ℚ
            translate-diff-zero-le-ℚ s t s<t =
              tr
                (λ u → le-ℚ u zero-ℚ)
                (distributive-neg-diff-ℚ t s)
                (neg-le-ℚ zero-ℚ (t -ℚ s) (backward-implication (iff-translate-diff-le-zero-ℚ s t) s<t))
```
