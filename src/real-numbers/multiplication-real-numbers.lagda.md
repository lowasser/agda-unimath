# Multiplication of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.posets

open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

We introduce
{{#concept "multiplication" Disambiguation="real numbers" Agda=mul-ℝ WDID=Q40276 WD="multiplication"}}
on the [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) and derive
its basic properties.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ q =
    ∃ ( type-enclosing-rational-interval-ℝ x ×
        type-enclosing-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        is-below-prop-interval-ℚ (mul-interval-ℚ [ax,bx] [ay,by]) q)

  upper-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ q =
    ∃ ( type-enclosing-rational-interval-ℝ x ×
        type-enclosing-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        is-above-prop-interval-ℚ (mul-interval-ℚ [ax,bx] [ay,by]) q)

  abstract
    is-inhabited-lower-cut-mul-ℝ : is-inhabited-subtype lower-cut-mul-ℝ
    is-inhabited-lower-cut-mul-ℝ =
      let open do-syntax-trunc-Prop (is-inhabited-subtype-Prop lower-cut-mul-ℝ)
      in do
        ([p,q] , p<x , x<q) ←
          is-inhabited-type-enclosing-rational-interval-ℝ x
        ([r,s] , r<y , y<s) ←
          is-inhabited-type-enclosing-rational-interval-ℝ y
        let min = lower-bound-interval-ℚ (mul-interval-ℚ [p,q] [r,s])
        (t , t<min) ← exists-lesser-ℚ min
        intro-exists
          ( t)
          ( intro-exists ((([p,q] , p<x , x<q) , ([r,s] , r<y , y<s))) t<min)

    is-inhabited-upper-cut-mul-ℝ : is-inhabited-subtype upper-cut-mul-ℝ
    is-inhabited-upper-cut-mul-ℝ =
      let open do-syntax-trunc-Prop (is-inhabited-subtype-Prop upper-cut-mul-ℝ)
      in do
        ([p,q] , p<x , x<q) ←
          is-inhabited-type-enclosing-rational-interval-ℝ x
        ([r,s] , r<y , y<s) ←
          is-inhabited-type-enclosing-rational-interval-ℝ y
        let max = upper-bound-interval-ℚ (mul-interval-ℚ [p,q] [r,s])
        (t , max<t) ← exists-greater-ℚ max
        intro-exists
          ( t)
          ( intro-exists ((([p,q] , p<x , x<q) , ([r,s] , r<y , y<s))) max<t)

    forward-implication-is-rounded-lower-cut-mul-ℝ :
      (v : ℚ) → is-in-subtype lower-cut-mul-ℝ v →
      exists ℚ (λ w → le-ℚ-Prop v w ∧ lower-cut-mul-ℝ w)
    forward-implication-is-rounded-lower-cut-mul-ℝ v v<xy =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ w → le-ℚ-Prop v w ∧ lower-cut-mul-ℝ w))
      in do
        ([a,b],[c,d]@(([a,b] , _ , _) , ([c,d] , _ , _)) , v<min) ← v<xy
        let min = lower-bound-interval-ℚ (mul-interval-ℚ [a,b] [c,d])
        intro-exists
          ( mediant-ℚ v min)
          ( le-left-mediant-ℚ v min v<min ,
            intro-exists [a,b],[c,d] (le-right-mediant-ℚ v min v<min))

    forward-implication-is-rounded-upper-cut-mul-ℝ :
      (v : ℚ) → is-in-subtype upper-cut-mul-ℝ v →
      exists ℚ (λ w → le-ℚ-Prop w v ∧ upper-cut-mul-ℝ w)
    forward-implication-is-rounded-upper-cut-mul-ℝ v xy<v =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ w → le-ℚ-Prop w v ∧ upper-cut-mul-ℝ w))
      in do
        ([a,b],[c,d]@(([a,b] , _ , _) , ([c,d] , _ , _)) , max<v) ← xy<v
        let max = upper-bound-interval-ℚ (mul-interval-ℚ [a,b] [c,d])
        intro-exists
          ( mediant-ℚ max v)
          ( le-right-mediant-ℚ max v max<v ,
            intro-exists [a,b],[c,d] (le-left-mediant-ℚ max v max<v))

    backward-implication-is-rounded-lower-cut-mul-ℝ :
      (v : ℚ) → exists ℚ (λ w → le-ℚ-Prop v w ∧ lower-cut-mul-ℝ w) →
      is-in-subtype lower-cut-mul-ℝ v
    backward-implication-is-rounded-lower-cut-mul-ℝ v ∃w =
      let open do-syntax-trunc-Prop (lower-cut-mul-ℝ v)
      in do
        (w , v<w , w<xy) ← ∃w
        ([a,b],[c,d] , w<min) ← w<xy
        intro-exists [a,b],[c,d] (transitive-le-ℚ v w _ w<min v<w)

    backward-implication-is-rounded-upper-cut-mul-ℝ :
      (v : ℚ) → exists ℚ (λ w → le-ℚ-Prop w v ∧ upper-cut-mul-ℝ w) →
      is-in-subtype upper-cut-mul-ℝ v
    backward-implication-is-rounded-upper-cut-mul-ℝ v ∃w =
      let open do-syntax-trunc-Prop (upper-cut-mul-ℝ v)
      in do
        (w , w<v , xy<w) ← ∃w
        ([a,b],[c,d] , max<w) ← xy<w
        intro-exists [a,b],[c,d] (transitive-le-ℚ _ w v w<v max<w)

    is-rounded-lower-cut-mul-ℝ :
      (v : ℚ) →
      ( (is-in-subtype lower-cut-mul-ℝ v) ↔
        (exists ℚ (λ w → le-ℚ-Prop v w ∧ lower-cut-mul-ℝ w)))
    is-rounded-lower-cut-mul-ℝ v =
      ( forward-implication-is-rounded-lower-cut-mul-ℝ v ,
        backward-implication-is-rounded-lower-cut-mul-ℝ v)

    is-rounded-upper-cut-mul-ℝ :
      (v : ℚ) →
      ( (is-in-subtype upper-cut-mul-ℝ v) ↔
        (exists ℚ (λ w → le-ℚ-Prop w v ∧ upper-cut-mul-ℝ w)))
    is-rounded-upper-cut-mul-ℝ v =
      ( forward-implication-is-rounded-upper-cut-mul-ℝ v ,
        backward-implication-is-rounded-upper-cut-mul-ℝ v)

    is-disjoint-lower-upper-cut-mul-ℝ :
      (q : ℚ) →
      ¬ (is-in-subtype lower-cut-mul-ℝ q × is-in-subtype upper-cut-mul-ℝ q)
    is-disjoint-lower-upper-cut-mul-ℝ q (q<xy , xy<q) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        ( ( ([a,b]@((a , b) , a≤b) , a<x , x<b) ,
            ([c,d]@((c , d) , c≤d) , c<y , y<d)) ,
          q<min-ac-ad-bc-bd) ← q<xy
        ( ( ([a',b']@((a' , b') , a'≤b') , a'<x , x<b') ,
            ([c',d']@((c' , d') , c'≤d') , c'<y , y<d')) ,
          max-a'c'-a'd'-b'c'-b'd'<q) ← xy<q
        let
          a'' = max-ℚ a a'
          c'' = max-ℚ c c'
        irreflexive-le-ℚ q
          ( transitive-le-ℚ q _ q
            ( concatenate-leq-le-ℚ _ _ q
              ( transitive-leq-ℚ _ _ _
                ( pr2
                  ( is-in-mul-interval-mul-is-in-interval-ℚ
                    ( [a',b'])
                    ( [c',d'])
                    ( a'')
                    ( c'')
                    ( leq-right-max-ℚ a a' ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ x a b' a<x x<b')
                        ( a'≤b'))
                    ( leq-right-max-ℚ _ _ ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ y c d' c<y y<d')
                        ( c'≤d'))))
                ( pr1
                  ( is-in-mul-interval-mul-is-in-interval-ℚ
                    ( [a,b])
                    ( [c,d])
                    ( a'')
                    ( c'')
                    ( leq-left-max-ℚ a a' ,
                      leq-max-leq-both-ℚ _ _ _
                        ( a≤b)
                        ( leq-lower-upper-cut-ℝ x a' b a'<x x<b))
                    ( leq-left-max-ℚ c c' ,
                      leq-max-leq-both-ℚ _ _ _
                        ( c≤d)
                        ( leq-lower-upper-cut-ℝ y c' d c'<y y<d)))))
              ( max-a'c'-a'd'-b'c'-b'd'<q))
            ( q<min-ac-ad-bc-bd))

  lower-real-mul-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-mul-ℝ =
    ( lower-cut-mul-ℝ ,
      is-inhabited-lower-cut-mul-ℝ ,
      is-rounded-lower-cut-mul-ℝ)

  upper-real-mul-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-mul-ℝ =
    ( upper-cut-mul-ℝ ,
      is-inhabited-upper-cut-mul-ℝ ,
      is-rounded-upper-cut-mul-ℝ)

  abstract
    is-arithmetically-located-mul-ℝ :
      is-arithmetically-located-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ
    is-arithmetically-located-mul-ℝ ε =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( close-bounds-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ ε))
      in do
        (Nx , bound-Nx) ← natural-bound-location-ℝ x one-ℚ⁺
        (Ny , bound-Ny) ← natural-bound-location-ℝ y one-ℚ⁺
        let
          N = max-ℕ Nx Ny
          -- To make sure we have values strictly < and > the min and max
          -- whose difference is strictly less than ε, we need to split
          -- out the epsilons a bunch to give ourselves wiggle room.
          (ε-max-min , ε-wiggle , ε-max-min+ε-wiggle=ε) = split-ℚ⁺ ε
          (ε-max-min-x , ε-max-min-y , ε-max-min-split) = split-ℚ⁺ ε-max-min
          εx =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( ε-max-min-x *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
          εy =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( ε-max-min-y *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
          (δ⁺@(δ , _) , δ+δ<ε-wiggle) = bound-double-le-ℚ⁺ ε-wiggle
        ((p , q) , q<p+εx , p<x , x<q) ← is-arithmetically-located-ℝ x εx
        ((r , s) , s<r+εy , r<y , y<s) ← is-arithmetically-located-ℝ y εy
        let
          p≤q = leq-lower-upper-cut-ℝ x p q p<x x<q
          r≤s = leq-lower-upper-cut-ℝ y r s r<y y<s
          q-p<εx : le-ℚ (q -ℚ p) (rational-ℚ⁺ εx)
          q-p<εx =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ q) (commutative-add-ℚ _ _) q<p+εx)
          q-p<1 =
            concatenate-le-leq-ℚ
              ( q -ℚ p)
              ( rational-ℚ⁺ εx)
              ( one-ℚ)
              ( q-p<εx)
              ( leq-left-min-ℚ⁺ _ _)
          s-r<εy : le-ℚ (s -ℚ r) (rational-ℚ⁺ εy)
          s-r<εy =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ s) (commutative-add-ℚ _ _) s<r+εy)
          s-r<1 =
            concatenate-le-leq-ℚ
              ( s -ℚ r)
              ( rational-ℚ⁺ εy)
              ( one-ℚ)
              ( s-r<εy)
              ( leq-left-min-ℚ⁺ _ _)
          open inequality-reasoning-Poset ℚ-Poset
          max|r||s|≤sN =
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)
              ≤ rational-ℕ Ny
                by
                  leq-le-ℚ
                    ( bound-Ny
                      ( (r , s) ,
                        tr
                          ( le-ℚ s)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ s-r<1) ,
                        r<y ,
                        y<s))
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (right-leq-max-ℕ _ _)
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
          max|p||q|≤sN =
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q)
              ≤ rational-ℕ Nx
                by
                  leq-le-ℚ
                    ( bound-Nx
                      ( (p , q) ,
                        tr
                          ( le-ℚ q)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ q-p<1) ,
                        p<x ,
                        x<q))
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (left-leq-max-ℕ _ _)
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
          a = min-ℚ (min-ℚ (p *ℚ r) (p *ℚ s)) (min-ℚ (q *ℚ r) (q *ℚ s))
          b = max-ℚ (max-ℚ (p *ℚ r) (p *ℚ s)) (max-ℚ (q *ℚ r) (q *ℚ s))
        intro-exists
          ( a -ℚ δ , b +ℚ δ)
          ( tr
            ( le-ℚ (b +ℚ δ))
            ( commutative-add-ℚ _ _)
            ( le-transpose-left-diff-ℚ _ _ _
              ( concatenate-leq-le-ℚ
                ( (b +ℚ δ) -ℚ (a -ℚ δ))
                ( rational-ℚ⁺ ε-max-min +ℚ (δ +ℚ δ))
                ( rational-ℚ⁺ ε)
                ( inv-tr
                  ( λ η → leq-ℚ η ( rational-ℚ⁺ ε-max-min +ℚ (δ +ℚ δ)))
                  ( ap-add-ℚ
                      ( refl)
                      ( distributive-neg-diff-ℚ _ _ ∙
                        commutative-add-ℚ _ _) ∙
                    interchange-law-add-add-ℚ _ _ _ _)
                  ( preserves-leq-left-add-ℚ _ _ _
                    ( chain-of-inequalities
                        b -ℚ a
                        ≤ ( (q -ℚ p) *ℚ
                            max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)) +ℚ
                          ( (s -ℚ r) *ℚ
                            max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
                          by
                            bound-width-mul-interval-ℚ
                              ( (p , q) , p≤q)
                              ( (r , s) , r≤s)
                        ≤ ( rational-ℚ⁺ εx *ℚ rational-ℕ (succ-ℕ N)) +ℚ
                          ( rational-ℚ⁺ εy *ℚ rational-ℕ (succ-ℕ N))
                          by
                            preserves-leq-add-ℚ
                              ( preserves-leq-mul-ℚ⁰⁺
                                ( nonnegative-diff-leq-ℚ _ _ p≤q)
                                ( nonnegative-ℚ⁺ εx)
                                ( max-ℚ⁰⁺ (abs-ℚ r) (abs-ℚ s))
                                ( nonnegative-rational-ℕ (succ-ℕ N))
                                ( leq-le-ℚ q-p<εx)
                                ( max|r||s|≤sN))
                              ( preserves-leq-mul-ℚ⁰⁺
                                ( nonnegative-diff-leq-ℚ _ _ r≤s)
                                ( nonnegative-ℚ⁺ εy)
                                ( max-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q))
                                ( nonnegative-rational-ℕ (succ-ℕ N))
                                ( leq-le-ℚ s-r<εy)
                                ( max|p||q|≤sN))
                        ≤ ( rational-ℚ⁺ εx +ℚ rational-ℚ⁺ εy) *ℚ
                          rational-ℕ (succ-ℕ N)
                          by
                            leq-eq-ℚ _ _
                              ( inv (right-distributive-mul-add-ℚ _ _ _))
                        ≤ rational-ℚ⁺
                            ( ( ε-max-min-x *ℚ⁺
                                positive-reciprocal-rational-succ-ℕ N) +ℚ⁺
                              ( ε-max-min-y *ℚ⁺
                                positive-reciprocal-rational-succ-ℕ N)) *ℚ
                          rational-ℕ (succ-ℕ N)
                          by
                            preserves-leq-right-mul-ℚ⁰⁺
                              ( nonnegative-rational-ℕ (succ-ℕ N))
                              ( _)
                              ( _)
                              ( preserves-leq-add-ℚ
                                ( leq-right-min-ℚ⁺ _ _)
                                ( leq-right-min-ℚ⁺ _ _))
                        ≤ rational-ℚ⁺ ε-max-min
                          by
                            leq-eq-ℚ _ _
                              ( ap-mul-ℚ
                                ( inv (right-distributive-mul-add-ℚ _ _ _))
                                ( refl) ∙
                                ap
                                  ( rational-ℚ⁺)
                                  ( is-section-right-mul-ℚ⁺
                                    ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' N))
                                    ( ε-max-min-x +ℚ⁺ ε-max-min-y) ∙
                                    ε-max-min-split)))))
                ( tr
                  ( le-ℚ⁺ (ε-max-min +ℚ⁺ (δ⁺ +ℚ⁺ δ⁺)))
                  ( ε-max-min+ε-wiggle=ε)
                  ( preserves-le-right-add-ℚ _ _ _ δ+δ<ε-wiggle)))) ,
            intro-exists
              ( (((p , q) , p≤q) , p<x , x<q) ,
                (((r , s) , r≤s) , r<y , y<s))
              ( le-diff-rational-ℚ⁺ a δ⁺) ,
            intro-exists
              ( (((p , q) , p≤q) , p<x , x<q) ,
                (((r , s) , r≤s) , r<y , y<s))
              ( le-right-add-rational-ℚ⁺ b δ⁺))

  abstract
    is-located-mul-ℝ :
      is-located-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ
    is-located-mul-ℝ =
      is-located-is-arithmetically-located-lower-upper-ℝ _ _
        ( is-arithmetically-located-mul-ℝ)

  opaque
    mul-ℝ : ℝ (l1 ⊔ l2)
    mul-ℝ =
      real-lower-upper-ℝ
        ( lower-real-mul-ℝ)
        ( upper-real-mul-ℝ)
        ( is-disjoint-lower-upper-cut-mul-ℝ)
        ( is-located-mul-ℝ)

infixl 40 _*ℝ_
_*ℝ_ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → ℝ (l1 ⊔ l2)
_*ℝ_ = mul-ℝ
```

## Properties

### Commutativity

```agda
opaque
  unfolding leq-ℝ mul-ℝ

  leq-commute-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    leq-ℝ (x *ℝ y) (y *ℝ x)
  leq-commute-mul-ℝ x y q q<xy =
    let open do-syntax-trunc-Prop (lower-cut-mul-ℝ y x q)
    in do
      ((([a,b] , a<x , x<b) , ([c,d] , c<y , y<d)) , q<[a,b][c,d]) ← q<xy
      intro-exists
        ( ([c,d] , c<y , y<d) , ([a,b] , a<x , x<b))
        ( tr
          ( λ i → is-below-interval-ℚ i q)
          ( commutative-mul-interval-ℚ [a,b] [c,d])
          ( q<[a,b][c,d]))

abstract
  commutative-mul-ℝ : {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → x *ℝ y ＝ y *ℝ x
  commutative-mul-ℝ x y =
    eq-sim-ℝ (sim-sim-leq-ℝ (leq-commute-mul-ℝ x y , leq-commute-mul-ℝ y x))
```

### The inclusion of rational numbers preserves multiplication

```agda
opaque
  unfolding mul-ℝ real-ℚ

  mul-real-ℚ : (p q : ℚ) → real-ℚ p *ℝ real-ℚ q ＝ real-ℚ (p *ℚ q)
  mul-real-ℚ p q =
    let open do-syntax-trunc-Prop empty-Prop
    in
      eq-sim-ℝ
        ( sim-rational-ℝ
          ( real-ℚ p *ℝ real-ℚ q ,
            p *ℚ q ,
            ( λ pq<pℝqℝ →
                do
                  ( (([a,b] , a<p , p<b) , ([c,d] , c<q , q<d)) ,
                    pq<[a,b][c,d]) ← pq<pℝqℝ
                  irreflexive-le-ℚ
                    ( p *ℚ q)
                    ( concatenate-le-leq-ℚ _ _ _
                      ( pq<[a,b][c,d])
                      ( pr1
                        ( is-in-mul-interval-mul-is-in-interval-ℚ
                          ( [a,b])
                          ( [c,d])
                          ( p)
                          ( q)
                          ( leq-le-ℚ a<p , leq-le-ℚ p<b)
                          ( leq-le-ℚ c<q , leq-le-ℚ q<d))))) ,
            ( λ pℝqℝ<pq →
              do
                ( (([a,b] , a<p , p<b) , ([c,d] , c<q , q<d)) ,
                    [a,b][c,d]<pq) ← pℝqℝ<pq
                irreflexive-le-ℚ
                  ( p *ℚ q)
                  ( concatenate-leq-le-ℚ _ _ _
                    ( pr2
                      ( is-in-mul-interval-mul-is-in-interval-ℚ
                        ( [a,b])
                        ( [c,d])
                        ( p)
                        ( q)
                        ( leq-le-ℚ a<p , leq-le-ℚ p<b)
                        ( leq-le-ℚ c<q , leq-le-ℚ q<d)))
                    ( [a,b][c,d]<pq)))))
```
