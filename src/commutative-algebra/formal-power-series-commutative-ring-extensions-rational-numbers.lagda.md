# Formal power series in commutative ring extensions of the rational numbers

```agda
module commutative-algebra.formal-power-series-commutative-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ring-extensions-rational-numbers
open import commutative-algebra.formal-power-series-commutative-rings

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import lists.sequences
```

</details>

## Idea

A
{{#concept "formal power series" WD="formal power series" WDID=Q1003025 disambiguation="in a commutative ring extension of the rational numbers" Agda=formal-power-series-Rational-Extension-Commutative-Ring}}
in a
[commutative ring extension of the rational numbers](commutative-algebra.commutative-ring-extensions-rational-numbers.md)
`R` is a formal sum of the form `Σₙ aₙxⁿ`, where `n` ranges over the
[natural numbers](elementary-number-theory.natural-numbers.md) and the
coefficients `aₙ` are elements of `R`, without any notion of convergence.

## Definition

```agda
formal-power-series-Rational-Extension-Commutative-Ring :
  {l : Level} → Rational-Extension-Commutative-Ring l → UU l
formal-power-series-Rational-Extension-Commutative-Ring R =
  formal-power-series-Commutative-Ring
    ( commutative-ring-Rational-Extension-Commutative-Ring R)

formal-power-series-coefficients-Rational-Extension-Commutative-Ring :
  {l : Level} → (R : Rational-Extension-Commutative-Ring l) →
  sequence (type-Rational-Extension-Commutative-Ring R) →
  formal-power-series-Rational-Extension-Commutative-Ring R
formal-power-series-coefficients-Rational-Extension-Commutative-Ring R =
  formal-power-series-coefficients-Commutative-Ring
    ( commutative-ring-Rational-Extension-Commutative-Ring R)

coefficient-formal-power-series-Rational-Extension-Commutative-Ring :
  {l : Level} (R : Rational-Extension-Commutative-Ring l) →
  (formal-power-series-Rational-Extension-Commutative-Ring R) →
  sequence (type-Rational-Extension-Commutative-Ring R)
coefficient-formal-power-series-Rational-Extension-Commutative-Ring R =
  coefficient-formal-power-series-Commutative-Ring
    ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

## Properties

### The set of formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  set-formal-power-series-Rational-Extension-Commutative-Ring : Set l
  set-formal-power-series-Rational-Extension-Commutative-Ring =
    set-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The constant term of a formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  constant-term-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R →
    type-Rational-Extension-Commutative-Ring R
  constant-term-formal-power-series-Rational-Extension-Commutative-Ring =
    constant-term-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The constant zero formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  zero-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R
  zero-formal-power-series-Rational-Extension-Commutative-Ring =
    zero-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The constant one formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  one-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R
  one-formal-power-series-Rational-Extension-Commutative-Ring =
    one-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The identity formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  id-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R
  id-formal-power-series-Rational-Extension-Commutative-Ring =
    id-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### Constant formal power series

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  constant-formal-power-series-Rational-Extension-Commutative-Ring :
    type-Rational-Extension-Commutative-Ring R →
    formal-power-series-Rational-Extension-Commutative-Ring R
  constant-formal-power-series-Rational-Extension-Commutative-Ring =
    constant-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The constant zero formal power series is the constant formal power series with value zero

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  constant-zero-formal-power-series-Rational-Extension-Commutative-Ring :
    constant-formal-power-series-Rational-Extension-Commutative-Ring R
      ( zero-Rational-Extension-Commutative-Ring R) ＝
    zero-formal-power-series-Rational-Extension-Commutative-Ring R
  constant-zero-formal-power-series-Rational-Extension-Commutative-Ring =
    constant-zero-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### The constant one formal power series is the constant formal power series with value zero

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  constant-one-formal-power-series-Rational-Extension-Commutative-Ring :
    constant-formal-power-series-Rational-Extension-Commutative-Ring R
      ( one-Rational-Extension-Commutative-Ring R) ＝
    one-formal-power-series-Rational-Extension-Commutative-Ring R
  constant-one-formal-power-series-Rational-Extension-Commutative-Ring =
    constant-one-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```

### Addition

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  add-formal-power-series-Rational-Extension-Commutative-Ring :
    formal-power-series-Rational-Extension-Commutative-Ring R →
    formal-power-series-Rational-Extension-Commutative-Ring R →
    formal-power-series-Rational-Extension-Commutative-Ring R
  add-formal-power-series-Rational-Extension-Commutative-Ring =
    add-formal-power-series-Commutative-Ring
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
```
