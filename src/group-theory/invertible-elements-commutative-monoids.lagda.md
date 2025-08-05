# Invertible elements in commutative monoids

```agda
module group-theory.invertible-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.invertible-elements-monoids
```

</details>

## Idea

An element `x : M` in a
[commutative monoid](group-theory.commutative-monoids.md) `M` is said to be
**left invertible** if there is an element `y : M` such that `yx ＝ e`, and it
is said to be **right invertible** if there is an element `y : M` such that
`xy ＝ e`. The element `x` is said to be **invertible** if it has a **two-sided
inverse**, i.e., if if there is an element `y : M` such that `xy = e` and
`yx = e`. Left inverses of elements are also called **retractions** and right
inverses are also called **sections**.

## Definitions

### Right invertible elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l) (x : type-Commutative-Monoid M)
  where

  is-right-inverse-element-Commutative-Monoid : type-Commutative-Monoid M → UU l
  is-right-inverse-element-Commutative-Monoid =
    is-right-inverse-element-Monoid (monoid-Commutative-Monoid M) x

  is-right-invertible-element-Commutative-Monoid : UU l
  is-right-invertible-element-Commutative-Monoid =
    is-right-invertible-element-Monoid (monoid-Commutative-Monoid M) x

module _
  {l : Level} (M : Commutative-Monoid l) {x : type-Commutative-Monoid M}
  where

  section-is-right-invertible-element-Commutative-Monoid :
    is-right-invertible-element-Commutative-Monoid M x →
    type-Commutative-Monoid M
  section-is-right-invertible-element-Commutative-Monoid = pr1

  is-right-inverse-section-is-right-invertible-element-Commutative-Monoid :
    (H : is-right-invertible-element-Commutative-Monoid M x) →
    is-right-inverse-element-Commutative-Monoid M x
      ( section-is-right-invertible-element-Commutative-Monoid H)
  is-right-inverse-section-is-right-invertible-element-Commutative-Monoid = pr2
```

### Left invertible elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l) (x : type-Commutative-Monoid M)
  where

  is-left-inverse-element-Commutative-Monoid : type-Commutative-Monoid M → UU l
  is-left-inverse-element-Commutative-Monoid =
    is-left-inverse-element-Monoid (monoid-Commutative-Monoid M) x

  is-left-invertible-element-Commutative-Monoid : UU l
  is-left-invertible-element-Commutative-Monoid =
    is-left-invertible-element-Monoid (monoid-Commutative-Monoid M) x

module _
  {l : Level} (M : Commutative-Monoid l) {x : type-Commutative-Monoid M}
  where

  retraction-is-left-invertible-element-Commutative-Monoid :
    is-left-invertible-element-Commutative-Monoid M x → type-Commutative-Monoid M
  retraction-is-left-invertible-element-Commutative-Monoid = pr1

  is-left-inverse-retraction-is-left-invertible-element-Commutative-Monoid :
    (H : is-left-invertible-element-Commutative-Monoid M x) →
    is-left-inverse-element-Commutative-Monoid M x
      ( retraction-is-left-invertible-element-Commutative-Monoid H)
  is-left-inverse-retraction-is-left-invertible-element-Commutative-Monoid = pr2
```

### Invertible elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l) (x : type-Commutative-Monoid M)
  where

  is-inverse-element-Commutative-Monoid : type-Commutative-Monoid M → UU l
  is-inverse-element-Commutative-Monoid =
    is-inverse-element-Monoid (monoid-Commutative-Monoid M) x

  is-invertible-element-Commutative-Monoid : UU l
  is-invertible-element-Commutative-Monoid =
    is-invertible-element-Monoid (monoid-Commutative-Monoid M) x

module _
  {l : Level} (M : Commutative-Monoid l) {x : type-Commutative-Monoid M}
  where

  inv-is-invertible-element-Commutative-Monoid :
    is-invertible-element-Commutative-Monoid M x → type-Commutative-Monoid M
  inv-is-invertible-element-Commutative-Monoid = pr1

  is-right-inverse-inv-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    is-right-inverse-element-Commutative-Monoid M x
      ( inv-is-invertible-element-Commutative-Monoid H)
  is-right-inverse-inv-is-invertible-element-Commutative-Monoid H = pr1 (pr2 H)

  is-left-inverse-inv-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    is-left-inverse-element-Commutative-Monoid M x
      ( inv-is-invertible-element-Commutative-Monoid H)
  is-left-inverse-inv-is-invertible-element-Commutative-Monoid H = pr2 (pr2 H)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-prop-is-invertible-element-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    is-prop (is-invertible-element-Commutative-Monoid M x)
  is-prop-is-invertible-element-Commutative-Monoid =
    is-prop-is-invertible-element-Monoid (monoid-Commutative-Monoid M)

  is-invertible-element-prop-Commutative-Monoid :
    type-Commutative-Monoid M → Prop l
  is-invertible-element-prop-Commutative-Monoid =
    is-invertible-element-prop-Monoid (monoid-Commutative-Monoid M)
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-left-invertible-is-invertible-element-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    is-invertible-element-Commutative-Monoid M x →
    is-left-invertible-element-Commutative-Monoid M x
  is-left-invertible-is-invertible-element-Commutative-Monoid =
    is-left-invertible-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)

  is-right-invertible-is-invertible-element-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    is-invertible-element-Commutative-Monoid M x → is-right-invertible-element-Commutative-Monoid M x
  is-right-invertible-is-invertible-element-Commutative-Monoid =
    is-right-invertible-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)
```

### The inverse invertible element

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-right-invertible-left-inverse-Commutative-Monoid :
    (x : type-Commutative-Monoid M)
    (lx : is-left-invertible-element-Commutative-Monoid M x) →
    is-right-invertible-element-Commutative-Monoid M (pr1 lx)
  is-right-invertible-left-inverse-Commutative-Monoid =
    is-right-invertible-left-inverse-Monoid (monoid-Commutative-Monoid M)

  is-left-invertible-right-inverse-Commutative-Monoid :
    (x : type-Commutative-Monoid M) (rx : is-right-invertible-element-Commutative-Monoid M x) →
    is-left-invertible-element-Commutative-Monoid M (pr1 rx)
  is-left-invertible-right-inverse-Commutative-Monoid =
    is-left-invertible-right-inverse-Monoid (monoid-Commutative-Monoid M)

  is-invertible-element-inverse-Commutative-Monoid :
    (x : type-Commutative-Monoid M) (x' : is-invertible-element-Commutative-Monoid M x) →
    is-invertible-element-Commutative-Monoid M (pr1 x')
  is-invertible-element-inverse-Commutative-Monoid =
    is-invertible-element-inverse-Monoid (monoid-Commutative-Monoid M)
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-contr-is-right-invertible-element-Commutative-Monoid :
    (x : type-Commutative-Monoid M) → is-invertible-element-Commutative-Monoid M x →
    is-contr (is-right-invertible-element-Commutative-Monoid M x)
  is-contr-is-right-invertible-element-Commutative-Monoid =
    is-contr-is-right-invertible-element-Monoid (monoid-Commutative-Monoid M)
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-contr-is-left-invertible-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    is-invertible-element-Commutative-Monoid M x →
    is-contr (is-left-invertible-element-Commutative-Monoid M x)
  is-contr-is-left-invertible-Commutative-Monoid =
    is-contr-is-left-invertible-Monoid (monoid-Commutative-Monoid M)
```

### The unit of a monoid is invertible

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-left-invertible-element-unit-Commutative-Monoid :
    is-left-invertible-element-Commutative-Monoid M (unit-Commutative-Monoid M)
  is-left-invertible-element-unit-Commutative-Monoid =
    is-left-invertible-element-unit-Monoid (monoid-Commutative-Monoid M)

  is-right-invertible-element-unit-Commutative-Monoid :
    is-right-invertible-element-Commutative-Monoid M (unit-Commutative-Monoid M)
  is-right-invertible-element-unit-Commutative-Monoid =
    is-right-invertible-element-unit-Monoid (monoid-Commutative-Monoid M)

  is-invertible-element-unit-Commutative-Monoid :
    is-invertible-element-Commutative-Monoid M (unit-Commutative-Monoid M)
  is-invertible-element-unit-Commutative-Monoid =
    is-invertible-element-unit-Monoid (monoid-Commutative-Monoid M)
```

### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-left-invertible-element-mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    is-left-invertible-element-Commutative-Monoid M x →
    is-left-invertible-element-Commutative-Monoid M y →
    is-left-invertible-element-Commutative-Monoid M
      ( mul-Commutative-Monoid M x y)
  is-left-invertible-element-mul-Commutative-Monoid =
    is-left-invertible-element-mul-Monoid (monoid-Commutative-Monoid M)

  is-right-invertible-element-mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    is-right-invertible-element-Commutative-Monoid M x →
    is-right-invertible-element-Commutative-Monoid M y →
    is-right-invertible-element-Commutative-Monoid M (mul-Commutative-Monoid M x y)
  is-right-invertible-element-mul-Commutative-Monoid =
    is-right-invertible-element-mul-Monoid (monoid-Commutative-Monoid M)

  is-invertible-element-mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    is-invertible-element-Commutative-Monoid M x →
    is-invertible-element-Commutative-Monoid M y →
    is-invertible-element-Commutative-Monoid M (mul-Commutative-Monoid M x y)
  is-invertible-element-mul-Commutative-Monoid =
    is-invertible-element-mul-Monoid (monoid-Commutative-Monoid M)
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-invertible-element-inv-is-invertible-element-Commutative-Monoid :
    {x : type-Commutative-Monoid M} →
    (H : is-invertible-element-Commutative-Monoid M x) →
    is-invertible-element-Commutative-Monoid M
      ( inv-is-invertible-element-Commutative-Monoid M H)
  is-invertible-element-inv-is-invertible-element-Commutative-Monoid =
    is-invertible-element-inv-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)
```

### An element is invertible if and only if multiplying by it is an equivalence

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {l : Level} (M : Commutative-Monoid l) {x : type-Commutative-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Commutative-Monoid :
    is-equiv (mul-Commutative-Monoid M x) → type-Commutative-Monoid M
  inv-is-invertible-element-is-equiv-mul-Commutative-Monoid =
    inv-is-invertible-element-is-equiv-mul-Monoid (monoid-Commutative-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid :
    (H : is-equiv (mul-Commutative-Monoid M x)) →
    mul-Commutative-Monoid M x
      ( inv-is-invertible-element-is-equiv-mul-Commutative-Monoid H) ＝
    unit-Commutative-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid
      ( monoid-Commutative-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid :
    (H : is-equiv (mul-Commutative-Monoid M x)) →
    mul-Commutative-Monoid M
      ( inv-is-invertible-element-is-equiv-mul-Commutative-Monoid H)
      ( x) ＝
    unit-Commutative-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid
      ( monoid-Commutative-Monoid M)

  is-invertible-element-is-equiv-mul-Commutative-Monoid :
    is-equiv (mul-Commutative-Monoid M x) →
    is-invertible-element-Commutative-Monoid M x
  is-invertible-element-is-equiv-mul-Commutative-Monoid =
    is-invertible-element-is-equiv-mul-Monoid (monoid-Commutative-Monoid M)

  left-div-is-invertible-element-Commutative-Monoid :
    is-invertible-element-Commutative-Monoid M x →
    type-Commutative-Monoid M → type-Commutative-Monoid M
  left-div-is-invertible-element-Commutative-Monoid =
    left-div-is-invertible-element-Monoid (monoid-Commutative-Monoid M)

  is-section-left-div-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    mul-Commutative-Monoid M x ∘
    left-div-is-invertible-element-Commutative-Monoid H ~
    id
  is-section-left-div-is-invertible-element-Commutative-Monoid =
    is-section-left-div-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)

  is-retraction-left-div-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    left-div-is-invertible-element-Commutative-Monoid H ∘
    mul-Commutative-Monoid M x ~
    id
  is-retraction-left-div-is-invertible-element-Commutative-Monoid =
    is-retraction-left-div-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)

  is-equiv-mul-is-invertible-element-Commutative-Monoid :
    is-invertible-element-Commutative-Monoid M x → is-equiv (mul-Commutative-Monoid M x)
  is-equiv-mul-is-invertible-element-Commutative-Monoid =
    is-equiv-mul-is-invertible-element-Monoid (monoid-Commutative-Monoid M)
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {l : Level} (M : Commutative-Monoid l) {x : type-Commutative-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' :
    is-equiv (mul-Commutative-Monoid' M x) → type-Commutative-Monoid M
  inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' =
    inv-is-invertible-element-is-equiv-mul-Monoid' (monoid-Commutative-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' :
    (H : is-equiv (mul-Commutative-Monoid' M x)) →
    mul-Commutative-Monoid M (inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' H) x ＝
    unit-Commutative-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'
      ( monoid-Commutative-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' :
    (H : is-equiv (mul-Commutative-Monoid' M x)) →
    mul-Commutative-Monoid M x
      ( inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' H) ＝
    unit-Commutative-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Commutative-Monoid' =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'
      ( monoid-Commutative-Monoid M)

  is-invertible-element-is-equiv-mul-Commutative-Monoid' :
    is-equiv (mul-Commutative-Monoid' M x) →
    is-invertible-element-Commutative-Monoid M x
  is-invertible-element-is-equiv-mul-Commutative-Monoid' =
    is-invertible-element-is-equiv-mul-Monoid' (monoid-Commutative-Monoid M)

  right-div-is-invertible-element-Commutative-Monoid :
    is-invertible-element-Commutative-Monoid M x →
    type-Commutative-Monoid M → type-Commutative-Monoid M
  right-div-is-invertible-element-Commutative-Monoid =
    right-div-is-invertible-element-Monoid (monoid-Commutative-Monoid M)

  is-section-right-div-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    mul-Commutative-Monoid' M x ∘
    right-div-is-invertible-element-Commutative-Monoid H ~
    id
  is-section-right-div-is-invertible-element-Commutative-Monoid =
    is-section-right-div-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)

  is-retraction-right-div-is-invertible-element-Commutative-Monoid :
    (H : is-invertible-element-Commutative-Monoid M x) →
    right-div-is-invertible-element-Commutative-Monoid H ∘
    mul-Commutative-Monoid' M x ~
    id
  is-retraction-right-div-is-invertible-element-Commutative-Monoid =
    is-retraction-right-div-is-invertible-element-Monoid
      ( monoid-Commutative-Monoid M)

  is-equiv-mul-is-invertible-element-Commutative-Monoid' :
    is-invertible-element-Commutative-Monoid M x →
    is-equiv (mul-Commutative-Monoid' M x)
  is-equiv-mul-is-invertible-element-Commutative-Monoid' =
    is-equiv-mul-is-invertible-element-Monoid' (monoid-Commutative-Monoid M)
```

## See also

- [Invertible elements in monoids](group-theory.invertible-elements-monoids.md)
