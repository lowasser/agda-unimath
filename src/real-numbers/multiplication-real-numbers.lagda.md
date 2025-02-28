# Multiplication of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.subtypes
open import foundation.empty-types
open import foundation.cartesian-product-types

open import real-numbers.dedekind-real-numbers
```

</details>

## Definition

```agda

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ q =
    ∃
      ( type-subtype (rational-bounds-ℝ x))
      ( λ ((a , b) , _) →
        ∃
          ( type-subtype (rational-bounds-ℝ y))
          ( λ ((c , d) , _) →
            le-ℚ-Prop q (min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))))

  is-inhabited-lower-cut-mul-ℝ : exists ℚ lower-cut-mul-ℝ
  is-inhabited-lower-cut-mul-ℝ =
    do
      ((a , b) , a<x , x<b) ← is-inhabited-rational-bounds-ℝ x
      ((c , d) , c<y , y<d) ← is-inhabited-rational-bounds-ℝ y
      let
        min-ac-ad = min-ℚ (a *ℚ c) (a *ℚ d)
        min-bc-bd = min-ℚ (b *ℚ c) (b *ℚ d)
        min = min-ℚ min-ac-ad min-bc-bd
      (q , q<min) ← exists-lesser-ℚ min
      intro-exists
        ( q)
        ( intro-exists
          ( (a , b) , a<x , x<b)
          ( intro-exists
            ( (c , d) , c<y , y<d)
            ( q<min)))
    where open do-syntax-trunc-Prop (∃ ℚ lower-cut-mul-ℝ)

  is-rounded-lower-cut-mul-ℝ :
    (q : ℚ) →
    is-in-subtype lower-cut-mul-ℝ q ↔
    exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r)
  pr1 (is-rounded-lower-cut-mul-ℝ q) q<mul =
    do
      (((a , b) , a<x , x<b) , ((c , d) , c<y , y<d) , q<min) ← q<mul
      let min = min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
      (r , q<r , r<min) ← dense-le-ℚ q min q<min
      intro-exists
        r
        ( q<r ,
          intro-exists
            ( (a , b) , a<x , x<b)
            ( intro-exists ((c , d) , c<y , y<d) r<min))
    where open do-syntax-trunc-Prop (∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r))
  pr2 (is-rounded-lower-cut-mul-ℝ q) ∃r =
    do
      (r , q<r , r<mul) ← ∃r
      (((a , b) , a<x , x<b) , ((c , d) , c<y , y<d) , r<min) ← r<mul
      intro-exists
        ( (a , b) , a<x , x<b)
        ( intro-exists
          ( (c , d) , c<y , y<d)
          ( transitive-le-ℚ q r _ r<min q<r))
    where open do-syntax-trunc-Prop (lower-cut-mul-ℝ q)

  upper-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ q =
    ∃
      ( type-subtype (rational-bounds-ℝ x))
      ( λ ((a , b) , _) →
        ∃
          ( type-subtype (rational-bounds-ℝ y))
          ( λ ((c , d) , _) →
            le-ℚ-Prop
              ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d))) q))

  is-inhabited-upper-cut-mul-ℝ : exists ℚ upper-cut-mul-ℝ
  is-inhabited-upper-cut-mul-ℝ =
    do
      ((a , b) , a<x , x<b) ← is-inhabited-rational-bounds-ℝ x
      ((c , d) , c<y , y<d) ← is-inhabited-rational-bounds-ℝ y
      (q , max<q) ←
        exists-greater-ℚ
          ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)))
      intro-exists
        ( q)
        ( intro-exists
          ( (a , b) , a<x , x<b)
          ( intro-exists
            ( (c , d) , c<y , y<d)
            ( max<q)))
    where open do-syntax-trunc-Prop (∃ ℚ lower-cut-mul-ℝ)

  is-rounded-upper-cut-mul-ℝ :
    (q : ℚ) →
    is-in-subtype upper-cut-mul-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p)
  pr1 (is-rounded-upper-cut-mul-ℝ q) mul<q =
    do
      (((a , b) , a<x , x<b) , ((c , d) , c<y , y<d) , max<q) ← mul<q
      (p , max<p , p<q) ←
        is-dense-ℚ
          ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)))
          ( q)
          ( max<q)
      intro-exists
        p
        ( p<q ,
          intro-exists
            ( (a , b) , a<x , x<b)
            ( intro-exists ((c , d) , c<y , y<d) max<p))
    where
      open do-syntax-trunc-Prop (∃ ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p))
  pr2 (is-rounded-upper-cut-mul-ℝ q) ∃p =
    do
      (p , p<q , mul<p) ← ∃p
      (((a , b) , a<x , x<b) , ((c , d) , c<y , y<d) , max<p) ← mul<p
      intro-exists
        ( (a , b) , a<x , x<b)
        ( intro-exists
          ( (c , d) , c<y , y<d)
          ( transitive-le-ℚ
            ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)))
            ( p)
            ( q)
            ( p<q)
            ( max<p)))
    where open-do-syntax-trunc-Prop (upper-cut-mul-ℝ q)

  is-disjoint-lower-upper-cut-mul-ℝ :
    (q : ℚ) →
    ¬ (is-in-subtype lower-cut-mul-ℝ q × is-in-subtype upper-cut-mul-ℝ q)
  is-disjoint-lower-upper-cut-mul-ℝ q (q<mul , mul<q) =
    do
      (((a , b) , a<x , x<b) , ((c , d) , c<y , y<d) , q<min) ← q<mul
      (((a' ,  b') , a'<x , x<b') , ((c' , d') , c'<y , y<d') , max<q) ← mul<q
      let
        a<b = le-lower-upper-cut-ℝ x a b a<x x<b
        a'<b = le-lower-upper-cut-ℝ x a' b a'<x x<b
        a<b' = le-lower-upper-cut-ℝ x a b' a<x x<b'
        a'<b' = le-lower-upper-cut-ℝ x a' b' a'<x x<b'
        a'' = max-ℚ a a'
        a''∈[a,b] : is-in-closed-interval-ℚ a b a''
        a''∈[a,b] =
          ( leq-left-max-ℚ a a' ,
            leq-le-ℚ a'' b (le-max-le-both-ℚ b a a' a<b a'<b))
        a''∈[a',b'] : is-in-closed-interval-ℚ a' b' a''
        a''∈[a',b'] =
          ( leq-right-max-ℚ a a' ,
            leq-le-ℚ a'' b' (le-max-le-both-ℚ b' a a' a<b' a'<b'))
        c<d = le-lower-upper-cut-ℝ y c d c<y y<d
        c<d' = le-lower-upper-cut-ℝ y c d' c<y y<d'
        c'<d = le-lower-upper-cut-ℝ y c' d c'<y y<d
        c'<d' = le-lower-upper-cut-ℝ y c' d' c'<y y<d'
        c''∈[c,d] : is-in-closed-interval-ℚ c d c''
        c''∈[c,d] =
          ( leq-left-max-ℚ c c' ,
            leq-le-ℚ c'' d (le-max-le-both-ℚ d c c' c<d c'<d))
        c''∈[c',d'] : is-in-closed-interval-ℚ c' d' c''
        c''∈[c',d'] =
          ( leq-right-max-ℚ c c' ,
            leq-le-ℚ c'' d' (le-max-le-both-ℚ d' c c' c<d' c'<d))
        (min-ac-ad-bc-bd≤a''c'' , _) =
          mul-closed-interval-closed-interval-ℚ
            a b a'' c d c'' a''∈[a,b] c''∈[c,d]
        (_ , a''c''≤max-a'c'-a'd'-b'c'-b'd') =
          mul-closed-interval-closed-interval-ℚ
            a' b' a'' c' d' c'' a''∈[a',b'] c''∈[c',d']
        min-ac-ad-bc-bd≤max-a'c'-a'd'-b'c'-b'd' =
          transitive-leq-ℚ
            ( min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
            ( a'' *ℚ c'')
            ( max-ℚ (max-ℚ (a' *ℚ c') (a' *ℚ d')) (max-ℚ (b' *ℚ c') (b' *ℚ d')))
            ( a''c''≤max-a'c'-a'd'-b'c'-b'd')
            ( min-ac-ad-bc-bd≤a''c'')
      irreflexive-le-ℚ
        ( q)
        ( transitive-le-ℚ
          ( q)
          ( min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
          ( q)
          ( concat-leq-le-ℚ
            ( min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
            ( max-ℚ (max-ℚ (a' *ℚ c') (a' *ℚ d')) (max-ℚ (b' *ℚ c') (b' *ℚ d')))
            ( q)
            ( min-ac-ad-bc-bd≤max-a'c'-a'd'-b'c'-b'd')
            ( max<q))
          ( q<min))
    where open do-syntax-trunc-Prop empty-Prop
```
