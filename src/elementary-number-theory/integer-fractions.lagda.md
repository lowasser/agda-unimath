# Integer fractions

```agda
module elementary-number-theory.integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import set-theory.countable-sets
```

</details>

## Idea

The type of {{#concept "integer fractions" Agda=fraction-ℤ}} is the type of
pairs `n/m` consisting of an integer `n` and a positive integer `m`. The type of
rational numbers is a retract of the type of fractions.

## Definitions

### The type of fractions

```agda
fraction-ℤ : UU lzero
fraction-ℤ = ℤ × positive-ℤ
```

### The numerator of a fraction

```agda
numerator-fraction-ℤ : fraction-ℤ → ℤ
numerator-fraction-ℤ x = pr1 x
```

### The denominator of a fraction

```agda
positive-denominator-fraction-ℤ : fraction-ℤ → positive-ℤ
positive-denominator-fraction-ℤ x = pr2 x

denominator-fraction-ℤ : fraction-ℤ → ℤ
denominator-fraction-ℤ x = pr1 (positive-denominator-fraction-ℤ x)

is-positive-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (denominator-fraction-ℤ x)
is-positive-denominator-fraction-ℤ x = pr2 (positive-denominator-fraction-ℤ x)
```

### Inclusion of the integers

```agda
in-fraction-ℤ : ℤ → fraction-ℤ
pr1 (in-fraction-ℤ x) = x
pr2 (in-fraction-ℤ x) = one-positive-ℤ
```

### Negative one, zero and one

```agda
neg-one-fraction-ℤ : fraction-ℤ
neg-one-fraction-ℤ = in-fraction-ℤ neg-one-ℤ

is-neg-one-fraction-ℤ : fraction-ℤ → UU lzero
is-neg-one-fraction-ℤ x = (x ＝ neg-one-fraction-ℤ)

zero-fraction-ℤ : fraction-ℤ
zero-fraction-ℤ = in-fraction-ℤ zero-ℤ

is-zero-fraction-ℤ : fraction-ℤ → UU lzero
is-zero-fraction-ℤ x = (x ＝ zero-fraction-ℤ)

is-nonzero-fraction-ℤ : fraction-ℤ → UU lzero
is-nonzero-fraction-ℤ k = ¬ (is-zero-fraction-ℤ k)

one-fraction-ℤ : fraction-ℤ
one-fraction-ℤ = in-fraction-ℤ one-ℤ

is-one-fraction-ℤ : fraction-ℤ → UU lzero
is-one-fraction-ℤ x = (x ＝ one-fraction-ℤ)
```

### The negative of an integer fraction

```agda
neg-fraction-ℤ : fraction-ℤ → fraction-ℤ
neg-fraction-ℤ (d , n) = (neg-ℤ d , n)
```

## Properties

### The double negation of an integer fraction is the original fraction

```agda
abstract
  neg-neg-fraction-ℤ : (x : fraction-ℤ) → neg-fraction-ℤ (neg-fraction-ℤ x) ＝ x
  neg-neg-fraction-ℤ (n , d) = ap (_, d) (neg-neg-ℤ n)
```

### Denominators are nonzero

```agda
abstract
  is-nonzero-denominator-fraction-ℤ :
    (x : fraction-ℤ) → is-nonzero-ℤ (denominator-fraction-ℤ x)
  is-nonzero-denominator-fraction-ℤ x =
    is-nonzero-is-positive-ℤ (is-positive-denominator-fraction-ℤ x)
```

### The type of fractions is a set

```agda
abstract
  is-set-fraction-ℤ : is-set fraction-ℤ
  is-set-fraction-ℤ = is-set-Σ is-set-ℤ (λ _ → is-set-positive-ℤ)

fraction-ℤ-Set : Set lzero
fraction-ℤ-Set = (fraction-ℤ , is-set-fraction-ℤ)
```

### Integer fractions have decidable equality

```agda
has-decidable-equality-fraction-ℤ :
  has-decidable-equality fraction-ℤ
has-decidable-equality-fraction-ℤ =
  has-decidable-equality-product
    ( has-decidable-equality-ℤ)
    ( has-decidable-equality-Σ
        ( has-decidable-equality-ℤ)
        ( λ x → has-decidable-equality-is-prop (is-prop-is-positive-ℤ x)))
```

### The similarity relation on integer fractions

```agda
sim-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
sim-fraction-ℤ-Prop x y =
  Id-Prop ℤ-Set
    ( ( numerator-fraction-ℤ x) *ℤ (denominator-fraction-ℤ y))
    ( ( numerator-fraction-ℤ y) *ℤ (denominator-fraction-ℤ x))

sim-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
sim-fraction-ℤ x y = type-Prop (sim-fraction-ℤ-Prop x y)

is-prop-sim-fraction-ℤ : (x y : fraction-ℤ) → is-prop (sim-fraction-ℤ x y)
is-prop-sim-fraction-ℤ x y = is-prop-type-Prop (sim-fraction-ℤ-Prop x y)

refl-sim-fraction-ℤ : is-reflexive sim-fraction-ℤ
refl-sim-fraction-ℤ x = refl

symmetric-sim-fraction-ℤ : is-symmetric sim-fraction-ℤ
symmetric-sim-fraction-ℤ x y r = inv r

abstract
  transitive-sim-fraction-ℤ : is-transitive sim-fraction-ℤ
  transitive-sim-fraction-ℤ x y z s r =
    is-injective-right-mul-ℤ
      ( denominator-fraction-ℤ y)
      ( is-nonzero-denominator-fraction-ℤ y)
      ( ( associative-mul-ℤ
          ( numerator-fraction-ℤ x)
          ( denominator-fraction-ℤ z)
          ( denominator-fraction-ℤ y)) ∙
        ( ap
          ( (numerator-fraction-ℤ x) *ℤ_)
          ( commutative-mul-ℤ
            ( denominator-fraction-ℤ z)
            ( denominator-fraction-ℤ y))) ∙
        ( inv
          ( associative-mul-ℤ
            ( numerator-fraction-ℤ x)
            ( denominator-fraction-ℤ y)
            ( denominator-fraction-ℤ z))) ∙
        ( ap ( _*ℤ (denominator-fraction-ℤ z)) r) ∙
        ( associative-mul-ℤ
          ( numerator-fraction-ℤ y)
          ( denominator-fraction-ℤ x)
          ( denominator-fraction-ℤ z)) ∙
        ( ap
          ( (numerator-fraction-ℤ y) *ℤ_)
          ( commutative-mul-ℤ
            ( denominator-fraction-ℤ x)
            ( denominator-fraction-ℤ z))) ∙
        ( inv
          ( associative-mul-ℤ
            ( numerator-fraction-ℤ y)
            ( denominator-fraction-ℤ z)
            ( denominator-fraction-ℤ x))) ∙
        ( ap (_*ℤ (denominator-fraction-ℤ x)) s) ∙
        ( associative-mul-ℤ
          ( numerator-fraction-ℤ z)
          ( denominator-fraction-ℤ y)
          ( denominator-fraction-ℤ x)) ∙
        ( ap
          ( (numerator-fraction-ℤ z) *ℤ_)
          ( commutative-mul-ℤ
            ( denominator-fraction-ℤ y)
            ( denominator-fraction-ℤ x))) ∙
        ( inv
          ( associative-mul-ℤ
            ( numerator-fraction-ℤ z)
            ( denominator-fraction-ℤ x)
            ( denominator-fraction-ℤ y))))

equivalence-relation-sim-fraction-ℤ : equivalence-relation lzero fraction-ℤ
pr1 equivalence-relation-sim-fraction-ℤ = sim-fraction-ℤ-Prop
pr1 (pr2 equivalence-relation-sim-fraction-ℤ) = refl-sim-fraction-ℤ
pr1 (pr2 (pr2 equivalence-relation-sim-fraction-ℤ)) = symmetric-sim-fraction-ℤ
pr2 (pr2 (pr2 equivalence-relation-sim-fraction-ℤ)) = transitive-sim-fraction-ℤ
```

### The negatives of two similar integer fractions are similar

```agda
module _
  (x y : fraction-ℤ)
  where

  abstract
    preserves-sim-neg-fraction-ℤ :
      sim-fraction-ℤ x y → sim-fraction-ℤ (neg-fraction-ℤ x) (neg-fraction-ℤ y)
    preserves-sim-neg-fraction-ℤ H =
      ( left-negative-law-mul-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ y)) ∙
      ( ap neg-ℤ H) ∙
      ( inv
        ( left-negative-law-mul-ℤ
          ( numerator-fraction-ℤ y)
          ( denominator-fraction-ℤ x)))
```

### Two integer fractions with zero numerator are similar

```agda
abstract
  sim-is-zero-numerator-fraction-ℤ :
    (x y : fraction-ℤ) →
    is-zero-ℤ (numerator-fraction-ℤ x) →
    is-zero-ℤ (numerator-fraction-ℤ y) →
    sim-fraction-ℤ x y
  sim-is-zero-numerator-fraction-ℤ x y H K =
    eq-is-zero-ℤ
    ( ap (_*ℤ (denominator-fraction-ℤ y)) H ∙
      left-zero-law-mul-ℤ (denominator-fraction-ℤ y))
    ( ap (_*ℤ (denominator-fraction-ℤ x)) K ∙
      left-zero-law-mul-ℤ (denominator-fraction-ℤ x))
```

### The greatest common divisor of the numerator and a denominator of a fraction is always a positive integer

```agda
abstract
  is-positive-gcd-numerator-denominator-fraction-ℤ :
    (x : fraction-ℤ) →
    is-positive-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
  is-positive-gcd-numerator-denominator-fraction-ℤ x =
    is-positive-gcd-is-positive-right-ℤ
      ( numerator-fraction-ℤ x)
      ( denominator-fraction-ℤ x)
      ( is-positive-denominator-fraction-ℤ x)

abstract
  is-nonzero-gcd-numerator-denominator-fraction-ℤ :
    (x : fraction-ℤ) →
    is-nonzero-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
  is-nonzero-gcd-numerator-denominator-fraction-ℤ x =
    is-nonzero-is-positive-ℤ
      ( is-positive-gcd-numerator-denominator-fraction-ℤ x)
```

### The set of integer fractions is countable

```agda
is-countable-fraction-ℤ : is-countable fraction-ℤ-Set
is-countable-fraction-ℤ =
  is-countable-product
    ( ℤ-Set)
    ( positive-ℤ-Set)
    ( is-countable-ℤ)
    ( is-countable-positive-ℤ)
```
