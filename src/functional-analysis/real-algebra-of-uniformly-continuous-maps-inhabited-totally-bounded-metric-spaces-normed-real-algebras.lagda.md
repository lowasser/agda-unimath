# The real algebra of uniformly continuous maps from inhabited, totally bounded metric spaces to normed real algebras

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.real-algebra-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.function-algebras-commutative-rings
open import commutative-algebra.subalgebras-commutative-rings
open import commutative-algebra.subsets-algebras-commutative-rings

open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.real-vector-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.supremum-norm-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras

open import linear-algebra.normed-real-algebras
open import linear-algebra.real-algebras
open import linear-algebra.real-vector-spaces-uniformly-continuous-maps-normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from an
[inhabited, totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
to a [normed real algebra](linear-algebra.normed-real-algebras.md) form a
[real algebra](linear-algebra.real-algebras.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (A : Normed-ℝ-Algebra l4 l5)
  (let _*A_ = mul-Normed-ℝ-Algebra A)
  (let _-A_ = diff-Normed-ℝ-Algebra A)
  (let dist-A = dist-Normed-ℝ-Algebra A)
  where

  map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra : UU (l1 ⊔ l5)
  map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    type-inhabited-totally-bounded-Metric-Space X → type-Normed-ℝ-Algebra A

  is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    subtype
      ( l1 ⊔ l2 ⊔ l4)
      ( map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-uniformly-continuous-prop-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Algebra A)

  is-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra →
    UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-in-subtype
      ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    UU (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    type-subtype
      ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  is-uniformly-continuous-const-zero-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
      ( λ _ → zero-Normed-ℝ-Algebra A)
  is-uniformly-continuous-const-zero-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-uniformly-continuous-const-zero-map-metric-space-Normed-ℝ-Vector-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( normed-vector-space-Normed-ℝ-Algebra A)

  is-closed-under-addition-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-closed-under-addition-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l4)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l4)
        ( type-inhabited-totally-bounded-Metric-Space X)
        ( algebra-Normed-ℝ-Algebra A))
      ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-closed-under-addition-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-closed-under-addition-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( normed-vector-space-Normed-ℝ-Algebra A)

  is-closed-under-scalar-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    is-closed-under-scalar-multiplication-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l4)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l4)
        ( type-inhabited-totally-bounded-Metric-Space X)
        ( algebra-Normed-ℝ-Algebra A))
      ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
  is-closed-under-scalar-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    is-closed-under-scalar-multiplication-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( normed-vector-space-Normed-ℝ-Algebra A)

  abstract
    is-closed-under-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
      is-closed-under-multiplication-subset-algebra-Commutative-Ring
        ( commutative-ring-ℝ l4)
        ( function-algebra-Commutative-Ring
          ( commutative-ring-ℝ l4)
          ( type-inhabited-totally-bounded-Metric-Space X)
          ( algebra-Normed-ℝ-Algebra A))
        ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
    is-closed-under-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
      f g uc-f uc-g =
      let
        open
          do-syntax-trunc-Prop
            ( is-uniformly-continuous-prop-map-Metric-Space
              ( metric-space-inhabited-totally-bounded-Metric-Space X)
              ( metric-space-Normed-ℝ-Algebra A)
              ( λ x → f x *A g x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        |f|⁰⁺@(|f| , _) =
          sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( f , uc-f)
        |g|⁰⁺@(|g| , _) =
          sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( g , uc-g)
        norm-A = map-norm-Normed-ℝ-Algebra A
      in do
        (μf , is-mod-μf) ← uc-f
        (μg , is-mod-μg) ← uc-g
        (q , |f|+|g|<q) ← exists-greater-positive-rational-ℝ (|f| +ℝ |g|)
        let
          μ ε = min-ℚ⁺ (μf (inv-ℚ⁺ q *ℚ⁺ ε)) (μg (inv-ℚ⁺ q *ℚ⁺ ε))
        intro-exists
          ( μ)
          ( λ x ε y Nμεxy →
            chain-of-inequalities
              dist-A (f x *A g x) (f y *A g y)
              ≤ dist-A (f x *A g x) (f x *A g y) +ℝ
                dist-A (f x *A g y) (f y *A g y)
                by triangular-dist-Normed-ℝ-Algebra A _ _ _
              ≤ norm-A (f x *A (g x -A g y)) +ℝ
                norm-A ((f x -A f y) *A g y)
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap
                        ( norm-A)
                        ( inv
                          ( left-distributive-mul-diff-Normed-ℝ-Algebra A
                            ( f x)
                            ( g x)
                            ( g y))))
                      ( ap
                        ( norm-A)
                        ( inv
                          ( right-distributive-mul-diff-Normed-ℝ-Algebra A
                            ( f x)
                            ( f y)
                            ( g y)))))
              ≤ norm-A (f x) *ℝ dist-A (g x) (g y) +ℝ
                dist-A (f x) (f y) *ℝ norm-A (g y)
                by
                  preserves-leq-add-ℝ
                    ( is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)
                    ( is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)
              ≤ |f| *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) +ℝ
                real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) *ℝ |g|
                by
                  preserves-leq-add-ℝ
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-norm-Normed-ℝ-Algebra A (f x))
                      ( |f|⁰⁺)
                      ( nonnegative-dist-Normed-ℝ-Algebra A (g x) (g y))
                      ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                      ( is-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
                        ( X)
                        ( A)
                        ( f , uc-f)
                        ( x))
                      ( is-mod-μg
                        ( x)
                        ( inv-ℚ⁺ q *ℚ⁺ ε)
                        ( y)
                        ( weakly-monotonic-neighborhood-Metric-Space
                          ( metric-space-inhabited-totally-bounded-Metric-Space
                            ( X))
                          ( x)
                          ( y)
                          ( μ ε)
                          ( μg (inv-ℚ⁺ q *ℚ⁺ ε))
                          ( leq-right-min-ℚ⁺
                            ( μf (inv-ℚ⁺ q *ℚ⁺ ε))
                            ( μg (inv-ℚ⁺ q *ℚ⁺ ε)))
                          ( Nμεxy))))
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-dist-Normed-ℝ-Algebra A (f x) (f y))
                      ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                      ( nonnegative-norm-Normed-ℝ-Algebra A (g y))
                      ( |g|⁰⁺)
                      ( is-mod-μf
                        ( x)
                        ( inv-ℚ⁺ q *ℚ⁺ ε)
                        ( y)
                        ( weakly-monotonic-neighborhood-Metric-Space
                          ( metric-space-inhabited-totally-bounded-Metric-Space
                            ( X))
                          ( x)
                          ( y)
                          ( μ ε)
                          ( μf (inv-ℚ⁺ q *ℚ⁺ ε))
                          ( leq-left-min-ℚ⁺
                            ( μf (inv-ℚ⁺ q *ℚ⁺ ε))
                            ( μg (inv-ℚ⁺ q *ℚ⁺ ε)))
                          ( Nμεxy)))
                      ( is-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
                        ( X)
                        ( A)
                        ( g , uc-g)
                        ( y)))
              ≤ |f| *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) +ℝ
                |g| *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)
                by leq-eq-ℝ (ap-add-ℝ refl (commutative-mul-ℝ _ _))
              ≤ (|f| +ℝ |g|) *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)
                by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
              ≤ real-ℚ⁺ q *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)
                by
                  preserves-leq-right-mul-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                    ( leq-le-ℝ |f|+|g|<q)
              ≤ real-ℚ⁺ (q *ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                by leq-eq-ℝ (mul-real-ℚ _ _)
              ≤ real-ℚ⁺ ε
                by leq-eq-ℝ (ap real-ℚ (is-section-left-div-ℚ⁺ q _)))

  subalgebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    subalgebra-Commutative-Ring
      ( l1 ⊔ l2 ⊔ l4)
      ( commutative-ring-ℝ l4)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l4)
        ( type-inhabited-totally-bounded-Metric-Space X)
        ( algebra-Normed-ℝ-Algebra A))
  subalgebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    ( is-uniformly-continuous-prop-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra ,
      is-uniformly-continuous-const-zero-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra ,
      is-closed-under-addition-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra ,
      is-closed-under-scalar-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra ,
      is-closed-under-multiplication-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    ℝ-Algebra l4 (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    algebra-subalgebra-Commutative-Ring
      ( commutative-ring-ℝ l4)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l4)
        ( type-inhabited-totally-bounded-Metric-Space X)
        ( algebra-Normed-ℝ-Algebra A))
      ( subalgebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra →
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra →
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
  mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    mul-ℝ-Algebra
      ( algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
```
