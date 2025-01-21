# Signs of real numbers

```agda
module real-numbers.sign-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

```agda
module _
  {l : Level} (x : ℝ l)
  where

  is-positive-ℝ : UU l
  is-positive-ℝ = is-in-lower-cut-ℝ x zero-ℚ

  is-zero-ℝ : UU l
  is-zero-ℝ = has-same-elements-subtype is-positive-prop-ℚ (upper-cut-ℝ x)

  is-negative-ℝ : UU l
  is-negative-ℝ = is-in-upper-cut-ℝ x zero-ℚ

  sign-ℝ : UU l
  sign-ℝ = is-negative-ℝ + (is-zero-ℝ + is-positive-ℝ)

  not-is-positive-and-negative : ¬ (is-positive-ℝ × is-negative-ℝ)
  not-is-positive-and-negative = is-disjoint-cut-ℝ x zero-ℚ

  not-is-zero-and-negative : ¬ (is-zero-ℝ × is-negative-ℝ)
  not-is-zero-and-negative (is-zero , is-neg) =
    is-nonzero-is-positive-ℚ (backward-implication (is-zero zero-ℚ) is-neg) refl

  not-is-zero-and-positive : ¬ (is-zero-ℝ × is-positive-ℝ)
  not-is-zero-and-positive (is-zero , is-pos) =
    elim-exists
      empty-Prop
      (λ q (0<q , in-lower-q) →
          is-disjoint-cut-ℝ x q (in-lower-q , forward-implication (is-zero q) (is-positive-le-zero-ℚ q 0<q)))
      (forward-implication (is-rounded-lower-cut-ℝ x zero-ℚ) is-pos)

  neg-lower-cut-ℝ : subtype l ℚ
  neg-lower-cut-ℝ q = upper-cut-ℝ x (neg-ℚ q)

  neg-upper-cut-ℝ : subtype l ℚ
  neg-upper-cut-ℝ q = lower-cut-ℝ x (neg-ℚ q)

  inhabited-neg-lower-cut-ℝ : exists ℚ neg-lower-cut-ℝ
  inhabited-neg-lower-cut-ℝ =
    elim-exists
      (∃ ℚ neg-lower-cut-ℝ)
      (λ q q-in-upper →
        intro-exists
          (neg-ℚ q)
          (tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ q)) q-in-upper))
      (is-inhabited-upper-cut-ℝ x)

  inhabited-neg-upper-cut-ℝ : exists ℚ neg-upper-cut-ℝ
  inhabited-neg-upper-cut-ℝ =
    elim-exists
      (∃ ℚ neg-upper-cut-ℝ)
      (λ q q-in-lower →
        intro-exists
          (neg-ℚ q)
          (tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q)) q-in-lower))
      (is-inhabited-lower-cut-ℝ x)

  is-rounded-neg-lower-cut-ℝ :
    (q : ℚ) →
    is-in-subtype neg-lower-cut-ℝ q ↔
    exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (neg-lower-cut-ℝ r))
  pr1 (is-rounded-neg-lower-cut-ℝ q) in-neg-lower =
    elim-exists
      (∃ ℚ (λ r → le-ℚ-Prop q r ∧ neg-lower-cut-ℝ r))
      (λ r (r<-q , in-upper-r) →
        intro-exists
          (neg-ℚ r)
          (tr
            (λ x → le-ℚ x (neg-ℚ r))
            (neg-neg-ℚ q)
            (neg-le-ℚ r (neg-ℚ q) r<-q) ,
           tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ r)) in-upper-r))
      (forward-implication (is-rounded-upper-cut-ℝ x (neg-ℚ q)) in-neg-lower)
  pr2 (is-rounded-neg-lower-cut-ℝ q) exists-r =
    backward-implication
      (is-rounded-upper-cut-ℝ x (neg-ℚ q))
      (elim-exists
        (∃ ℚ (λ r → le-ℚ-Prop r (neg-ℚ q) ∧ upper-cut-ℝ x r))
        (λ r (q<r , in-neg-lower-r) →
          intro-exists (neg-ℚ r) (neg-le-ℚ q r q<r , in-neg-lower-r))
        exists-r)

  is-rounded-neg-upper-cut-ℝ :
    (r : ℚ) →
    is-in-subtype neg-upper-cut-ℝ r ↔
    exists ℚ (λ q → (le-ℚ-Prop q r) ∧ (neg-upper-cut-ℝ q))
  pr1 (is-rounded-neg-upper-cut-ℝ r) in-neg-upper =
    elim-exists
      (∃ ℚ (λ q → le-ℚ-Prop q r ∧ neg-upper-cut-ℝ q))
      (λ q (-r<q , in-lower-q) →
        intro-exists
          (neg-ℚ q)
          (tr (le-ℚ (neg-ℚ q)) (neg-neg-ℚ r) (neg-le-ℚ (neg-ℚ r) q -r<q) ,
            tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q)) in-lower-q))
      (forward-implication (is-rounded-lower-cut-ℝ x (neg-ℚ r)) in-neg-upper)
  pr2 (is-rounded-neg-upper-cut-ℝ r) exists-q =
    backward-implication
      (is-rounded-lower-cut-ℝ x (neg-ℚ r))
      (elim-exists
        (∃ ℚ (λ q → le-ℚ-Prop (neg-ℚ r) q ∧ lower-cut-ℝ x q))
        (λ q (q<r , in-neg-upper-q) →
          intro-exists (neg-ℚ q) (neg-le-ℚ q r q<r , in-neg-upper-q))
        exists-q)

signed-ℝ : (l : Level) → UU (lsuc l)
signed-ℝ l = Σ (ℝ l) sign-ℝ
```
