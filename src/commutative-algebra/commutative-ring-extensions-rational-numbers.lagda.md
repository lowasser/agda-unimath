# Commutative ring extensions of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module commutative-algebra.commutative-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings

open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "commutative ring extension of ℚ" Agda=Rational-Extension-Commutative-Ring}}
is a [commutative ring](commutative-algebra.commutative-rings.md) that is a
[ring extension of ℚ](ring-theory.ring-extensions-rational-numbers.md).

## Definition

```agda
is-rational-ring-extension-prop-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → Prop l
is-rational-ring-extension-prop-Commutative-Ring R =
  is-rational-extension-prop-Ring (ring-Commutative-Ring R)

is-rational-ring-extension-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → UU l
is-rational-ring-extension-Commutative-Ring R =
  type-Prop (is-rational-ring-extension-prop-Commutative-Ring R)

Rational-Extension-Commutative-Ring : (l : Level) → UU (lsuc l)
Rational-Extension-Commutative-Ring l =
  type-subtype (is-rational-ring-extension-prop-Commutative-Ring {l})

module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  commutative-ring-Rational-Extension-Commutative-Ring : Commutative-Ring l
  commutative-ring-Rational-Extension-Commutative-Ring = pr1 R

  ring-Rational-Extension-Commutative-Ring : Ring l
  ring-Rational-Extension-Commutative-Ring =
    ring-Commutative-Ring commutative-ring-Rational-Extension-Commutative-Ring

  is-rational-extension-ring-Rational-Extension-Commutative-Ring :
    is-rational-extension-Ring ring-Rational-Extension-Commutative-Ring
  is-rational-extension-ring-Rational-Extension-Commutative-Ring = pr2 R

  rational-extension-ring-Rational-Extension-Commutative-Ring :
    Rational-Extension-Ring l
  rational-extension-ring-Rational-Extension-Commutative-Ring =
    ( ring-Rational-Extension-Commutative-Ring ,
      is-rational-extension-ring-Rational-Extension-Commutative-Ring)
```

## Properties

### The unique commutative ring homomorphism from `ℚ` to a commutative rational ring extension of `ℚ`

```agda
module _
  {l : Level} (R : Rational-Extension-Commutative-Ring l)
  where

  initial-hom-Rational-Extension-Commutative-Ring :
    hom-Commutative-Ring
      ( commutative-ring-ℚ)
      ( commutative-ring-Rational-Extension-Commutative-Ring R)
  initial-hom-Rational-Extension-Commutative-Ring =
    initial-hom-Rational-Extension-Ring
      ( rational-extension-ring-Rational-Extension-Commutative-Ring R)

  is-contr-rational-hom-Rational-Extension-Commutative-Ring :
    is-contr
      ( hom-Commutative-Ring
        ( commutative-ring-ℚ)
        ( commutative-ring-Rational-Extension-Commutative-Ring R))
  is-contr-rational-hom-Rational-Extension-Commutative-Ring =
    is-contr-rational-hom-Rational-Extension-Ring
      ( rational-extension-ring-Rational-Extension-Commutative-Ring R)
```

### A commutative ring `R` is a commutative ring extension of `ℚ` if and only if there is a commutative ring homomorphism from `ℚ` to `R`

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  iff-is-rational-extension-has-rational-hom-Commutative-Ring :
    hom-Commutative-Ring commutative-ring-ℚ R ↔
    is-rational-ring-extension-Commutative-Ring R
  iff-is-rational-extension-has-rational-hom-Commutative-Ring =
    iff-is-rational-extension-has-rational-hom-Ring (ring-Commutative-Ring R)
```
