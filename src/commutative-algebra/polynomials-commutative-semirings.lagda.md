# Polynomials series on commutative semirings

```agda
module commutative-algebra.polynomials-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

## Definition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  degree-bound-prop-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R →
    (n : ℕ) → Prop l
  degree-bound-prop-formal-power-series-Commutative-Semiring p n =
    Π-Prop
      ( ℕ)
      ( λ m →
        leq-ℕ-Prop n m ⇒
        is-zero-Commutative-Semiring-Prop
          ( R)
          ( coefficient-formal-power-series-Commutative-Semiring R p m))

  degree-bound-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R →
    (n : ℕ) →
    UU l
  degree-bound-formal-power-series-Commutative-Semiring p n =
    type-Prop (degree-bound-prop-formal-power-series-Commutative-Semiring p n)

  tail-degree-bound-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) (n : ℕ) →
    degree-bound-formal-power-series-Commutative-Semiring p (succ-ℕ n) →
    degree-bound-formal-power-series-Commutative-Semiring
      (tail-formal-power-series-Commutative-Semiring R p)
      n
  tail-degree-bound-formal-power-series-Commutative-Semiring p n H m m≤n =
    coefficient-formal-power-series-coefficients-Commutative-Semiring R _ m ∙
    H (succ-ℕ m) m≤n

  zero-degree-bound-iff-zero-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) →
    (degree-bound-formal-power-series-Commutative-Semiring p zero-ℕ) ↔
    (p ＝ zero-formal-power-series-Commutative-Semiring R)
  pr1 (zero-degree-bound-iff-zero-formal-power-series-Commutative-Semiring p)
    H =
      eq-htpy-coefficients-formal-power-series-Commutative-Semiring R _ _
        ( λ n →
          H n (leq-zero-ℕ n) ∙
          inv
            ( htpy-coefficient-zero-formal-power-series-Commutative-Semiring
              ( R)
              ( n)))
  pr2 (zero-degree-bound-iff-zero-formal-power-series-Commutative-Semiring _)
    refl m _ =
      htpy-coefficient-zero-formal-power-series-Commutative-Semiring R m

  one-degree-bound-iff-constant-formal-power-series-Commutative-Semiring :
    ( p : formal-power-series-Commutative-Semiring R) →
    ( degree-bound-formal-power-series-Commutative-Semiring p 1) ↔
    ( p ＝
      constant-formal-power-series-Commutative-Semiring
        ( R)
        ( constant-term-formal-power-series-Commutative-Semiring R p))
  pr1 (one-degree-bound-iff-constant-formal-power-series-Commutative-Semiring p)
    H =
      eq-htpy-coefficients-formal-power-series-Commutative-Semiring R _ _
        ( λ {
          zero-ℕ →
            inv
              ( htpy-coefficient-constant-formal-power-series-Commutative-Semiring
                ( R)
                ( _)
                ( 0)) ;
          (succ-ℕ n) →
            H (succ-ℕ n) star ∙
            inv
              ( htpy-coefficient-constant-formal-power-series-Commutative-Semiring
                ( R)
                ( _)
                ( _)) })
  pr2 (one-degree-bound-iff-constant-formal-power-series-Commutative-Semiring _)
    H (succ-ℕ n) K =
      ap
        ( λ q →
          coefficient-formal-power-series-Commutative-Semiring R q (succ-ℕ n))
        ( H) ∙
      htpy-coefficient-constant-formal-power-series-Commutative-Semiring
        ( R)
        ( _)
        ( succ-ℕ n)

  opaque
    is-polynomial-prop-Commutative-Semiring :
      subtype l (formal-power-series-Commutative-Semiring R)
    is-polynomial-prop-Commutative-Semiring p =
      ∃ ( ℕ)
        ( degree-bound-prop-formal-power-series-Commutative-Semiring p)

    polynomial-Commutative-Semiring : UU l
    polynomial-Commutative-Semiring =
      type-subtype is-polynomial-prop-Commutative-Semiring

    polynomial-degree-bound-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) (n : ℕ) →
      degree-bound-formal-power-series-Commutative-Semiring p n →
      polynomial-Commutative-Semiring
    polynomial-degree-bound-formal-power-series-Commutative-Semiring p n bound =
      p , intro-exists n bound

    formal-power-series-polynomial-Commutative-Semiring :
      polynomial-Commutative-Semiring →
      formal-power-series-Commutative-Semiring R
    formal-power-series-polynomial-Commutative-Semiring =
      inclusion-subtype is-polynomial-prop-Commutative-Semiring

    exists-degree-bound-formal-power-series-polynomial-Commutative-Semiring :
      (p : polynomial-Commutative-Semiring) →
      exists
        ( ℕ)
        ( degree-bound-prop-formal-power-series-Commutative-Semiring
          ( formal-power-series-polynomial-Commutative-Semiring p))
    exists-degree-bound-formal-power-series-polynomial-Commutative-Semiring =
      pr2

    eq-formal-power-series-polynomial-degree-bound-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) (n : ℕ) →
      (H : degree-bound-formal-power-series-Commutative-Semiring p n) →
      formal-power-series-polynomial-Commutative-Semiring
        ( polynomial-degree-bound-formal-power-series-Commutative-Semiring
          ( p)
          ( n)
          ( H)) ＝ p
    eq-formal-power-series-polynomial-degree-bound-formal-power-series-Commutative-Semiring
      p _ _ = refl
```

## Properties

### Evaluation of polynomials

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  ev-formal-power-series-degree-bound-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) (n : ℕ) →
    degree-bound-formal-power-series-Commutative-Semiring R p n →
    type-Commutative-Semiring R → type-Commutative-Semiring R
  ev-formal-power-series-degree-bound-Commutative-Semiring p zero-ℕ _ _ =
    zero-Commutative-Semiring R
  ev-formal-power-series-degree-bound-Commutative-Semiring p (succ-ℕ n) H x =
    add-Commutative-Semiring
      ( R)
      ( constant-term-formal-power-series-Commutative-Semiring R p)
      ( mul-Commutative-Semiring R
        ( x)
        ( ev-formal-power-series-degree-bound-Commutative-Semiring
          ( tail-formal-power-series-Commutative-Semiring R p)
          ( n)
          ( tail-degree-bound-formal-power-series-Commutative-Semiring R p n H)
          ( x)))

  opaque
    unfolding zero-formal-power-series-Commutative-Semiring

    ev-zero-formal-power-series-degree-bound-Commutative-Semiring :
      (n : ℕ) →
      (H :
        degree-bound-formal-power-series-Commutative-Semiring
          ( R)
          ( zero-formal-power-series-Commutative-Semiring R)
          ( n)) →
      (x : type-Commutative-Semiring R) →
      ev-formal-power-series-degree-bound-Commutative-Semiring
        ( zero-formal-power-series-Commutative-Semiring R)
        ( n)
        ( H)
        ( x) ＝
      zero-Commutative-Semiring R
    ev-zero-formal-power-series-degree-bound-Commutative-Semiring zero-ℕ _ _ =
      refl
    ev-zero-formal-power-series-degree-bound-Commutative-Semiring
      (succ-ℕ n) H x =
        equational-reasoning
          add-Commutative-Semiring
            ( R)
            ( coefficient-formal-power-series-Commutative-Semiring R
              ( zero-formal-power-series-Commutative-Semiring R)
              ( zero-ℕ))
            ( mul-Commutative-Semiring
              ( R)
              ( x)
              ( ev-formal-power-series-degree-bound-Commutative-Semiring
                ( zero-formal-power-series-Commutative-Semiring R)
                ( n)
                ( tail-degree-bound-formal-power-series-Commutative-Semiring
                  ( R)
                  ( zero-formal-power-series-Commutative-Semiring R)
                  ( n)
                  ( H))
                ( x)))
          ＝
            add-Commutative-Semiring
              ( R)
              ( zero-Commutative-Semiring R)
              ( mul-Commutative-Semiring R x (zero-Commutative-Semiring R))
            by
              ap-add-Commutative-Semiring
                ( R)
                ( htpy-coefficient-zero-formal-power-series-Commutative-Semiring
                  ( R)
                  ( zero-ℕ))
                ( ap-mul-Commutative-Semiring
                  ( R)
                  ( refl)
                  ( ev-zero-formal-power-series-degree-bound-Commutative-Semiring
                    ( n)
                    ( tail-degree-bound-formal-power-series-Commutative-Semiring
                      ( R)
                      ( zero-formal-power-series-Commutative-Semiring R)
                      ( n)
                      ( H))
                    ( x)))
          ＝ mul-Commutative-Semiring R x (zero-Commutative-Semiring R)
            by left-unit-law-add-Commutative-Semiring R _
          ＝ zero-Commutative-Semiring R
            by right-zero-law-mul-Commutative-Semiring R _

  abstract
    ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) →
      (nH : ℕ) →
      (H : degree-bound-formal-power-series-Commutative-Semiring R p nH) →
      (nK : ℕ) →
      (K : degree-bound-formal-power-series-Commutative-Semiring R p nK) →
      ev-formal-power-series-degree-bound-Commutative-Semiring p nH H ~
      ev-formal-power-series-degree-bound-Commutative-Semiring p nK K
    ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring
      p zero-ℕ H nK K x
      with
        forward-implication
          ( zero-degree-bound-iff-zero-formal-power-series-Commutative-Semiring
            ( R)
            ( p))
          ( H)
    ... | refl =
      ev-zero-formal-power-series-degree-bound-Commutative-Semiring 0 H x ∙
      inv
        ( ev-zero-formal-power-series-degree-bound-Commutative-Semiring nK K x)
    ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring
      p (succ-ℕ nH) H zero-ℕ K x
      with
        forward-implication
          ( zero-degree-bound-iff-zero-formal-power-series-Commutative-Semiring
            ( R)
            ( p))
          ( K)
    ... | refl =
      ev-zero-formal-power-series-degree-bound-Commutative-Semiring
        ( succ-ℕ nH)
        ( H)
        ( x) ∙
      inv (ev-zero-formal-power-series-degree-bound-Commutative-Semiring 0 K x)
    ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring
      p (succ-ℕ nH) H (succ-ℕ nK) K x =
        ap-add-Commutative-Semiring R
          ( refl)
          ( ap-mul-Commutative-Semiring R refl
            ( ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring
              ( _)
              nH
              ( tail-degree-bound-formal-power-series-Commutative-Semiring
                ( R)
                ( p)
                ( nH)
                ( H))
              ( nK)
              ( tail-degree-bound-formal-power-series-Commutative-Semiring
                ( R)
                ( p)
                ( nK)
                ( K))
              ( x)))

  ev-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R → type-Commutative-Semiring R →
    type-Commutative-Semiring R
  ev-polynomial-Commutative-Semiring p x =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Semiring R)
      ( λ H →
        ind-Σ
          ( ev-formal-power-series-degree-bound-Commutative-Semiring
            ( formal-power-series-polynomial-Commutative-Semiring R p))
          ( H)
          ( x))
      ( λ (nH , H) (nK , K) →
        ev-degree-bounds-formal-power-series-degree-bound-Commutative-Semiring
          ( formal-power-series-polynomial-Commutative-Semiring R p)
          ( nH)
          ( H)
          ( nK)
          ( K)
          ( x))
      ( exists-degree-bound-formal-power-series-polynomial-Commutative-Semiring
        ( R)
        ( p))

  ev-polynomial-degree-bound-Commutative-Semiring :
    (p : polynomial-Commutative-Semiring R) (n : ℕ) →
    (H :
      degree-bound-formal-power-series-Commutative-Semiring
        ( R)
        ( formal-power-series-polynomial-Commutative-Semiring R p)
        ( n)) →
    ev-polynomial-Commutative-Semiring p ~
    ev-formal-power-series-degree-bound-Commutative-Semiring
      ( formal-power-series-polynomial-Commutative-Semiring R p)
      ( n)
      ( H)
```

### Constant polynomials

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (c : type-Commutative-Semiring R)
  where

  one-degree-bound-constant-formal-power-series-Commutative-Semiring :
    degree-bound-formal-power-series-Commutative-Semiring
      ( R)
      ( constant-formal-power-series-Commutative-Semiring R c)
      1
  one-degree-bound-constant-formal-power-series-Commutative-Semiring =
    backward-implication
      ( one-degree-bound-iff-constant-formal-power-series-Commutative-Semiring
        ( R)
        ( constant-formal-power-series-Commutative-Semiring R c))
      ( ap
        ( constant-formal-power-series-Commutative-Semiring R)
        ( inv
          ( htpy-coefficient-constant-formal-power-series-Commutative-Semiring
            ( R)
            ( c)
            ( 0))))

  constant-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  constant-polynomial-Commutative-Semiring =
    polynomial-degree-bound-formal-power-series-Commutative-Semiring
      ( R)
      ( constant-formal-power-series-Commutative-Semiring R c)
      ( 1)
      ( one-degree-bound-constant-formal-power-series-Commutative-Semiring)

  ev-constant-polynomial-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    ev-polynomial-Commutative-Semiring
      ( R)
      ( constant-polynomial-Commutative-Semiring)
      ( x) ＝
    c
  ev-constant-polynomial-Commutative-Semiring x =
    equational-reasoning
      ev-polynomial-Commutative-Semiring
        ( R)
        ( constant-polynomial-Commutative-Semiring)
        ( x)
      ＝
        ev-formal-power-series-degree-bound-Commutative-Semiring
          ( R)
          {!   !}
          ( 1)
          ( one-degree-bound-constant-formal-power-series-Commutative-Semiring)
          ( x)
        by {!   !}
      ＝ {!   !} by {!   !}
```
