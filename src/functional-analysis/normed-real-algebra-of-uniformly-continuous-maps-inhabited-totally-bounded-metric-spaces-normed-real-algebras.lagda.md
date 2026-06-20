# The normed real algebra of uniformly continuous maps from inhabited, totally bounded metric spaces to normed real algebras

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.normed-real-algebra-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.normed-real-vector-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.real-algebra-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras
open import functional-analysis.supremum-norm-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras

open import linear-algebra.normed-real-algebras

open import metric-spaces.inhabited-totally-bounded-metric-spaces

open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.suprema-families-nonnegative-real-numbers
```

</details>

## Idea

The
[supremum norm](functional-analysis.supremum-norm-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras.md)
on
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from an
[inhabited, totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
to a [normed real algebra](linear-algebra.normed-real-algebras.md) is a norm on
the
[real algebra of those maps](functional-analysis.real-algebra-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-algebras.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (A : Normed-ℝ-Algebra l4 l5)
  where

  abstract
    is-submultiplicative-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
      is-submultiplicative-norm-vector-space-ℝ-Algebra
        ( algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
          ( X)
          ( A))
        ( norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( normed-vector-space-Normed-ℝ-Algebra A))
    is-submultiplicative-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
      f@(map-f , _) g@(map-g , _) =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        norm-A = map-norm-Normed-ℝ-Algebra A
        norm-A⁰⁺ = nonnegative-norm-Normed-ℝ-Algebra A
        _*A_ = mul-Normed-ℝ-Algebra A
        fg =
          mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( f)
            ( g)
        (|f|⁰⁺@(|f| , _) , is-ub-f , _) =
          has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( f)
        (|g|⁰⁺@(|g| , _) , is-ub-g , _) =
          has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( g)
      in
        leq-is-least-upper-bound-family-of-elements-Large-Poset
          ( large-poset-ℝ⁰⁺)
          ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( fg))
          ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( fg))
          ( is-least-upper-bound-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
            ( X)
            ( A)
            ( fg))
          ( |f|⁰⁺ *ℝ⁰⁺ |g|⁰⁺)
          ( λ x →
            chain-of-inequalities
              norm-A (map-f x *A map-g x)
              ≤ norm-A (map-f x) *ℝ norm-A (map-g x)
                by is-submultiplicative-norm-Normed-ℝ-Algebra A _ _
              ≤ |f| *ℝ |g|
                by
                  preserves-leq-mul-ℝ⁰⁺
                    ( norm-A⁰⁺ (map-f x))
                    ( |f|⁰⁺)
                    ( norm-A⁰⁺ (map-g x))
                    ( |g|⁰⁺)
                    ( is-ub-f x)
                    ( is-ub-g x))

  norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    norm-ℝ-Algebra
      ( algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
        ( X)
        ( A))
  norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    ( norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( normed-vector-space-Normed-ℝ-Algebra A) ,
      is-submultiplicative-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)

  normed-algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra :
    Normed-ℝ-Algebra l4 (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  normed-algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra =
    ( algebra-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra
        ( X)
        ( A) ,
      norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Algebra)
```
