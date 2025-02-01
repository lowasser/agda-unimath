# Multiplication on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.transport-along-identifications
```

</details>

## Idea

**Multiplication on integer fractions** is an extension of the
[multiplicative operation](elementary-number-theory.multiplication-integers.md)
on the [integers](elementary-number-theory.integers.md) to
[integer fractions](elementary-number-theory.integer-fractions.md). Note that
the basic properties of multiplication on integer fraction only hold up to
fraction similarity.

## Definition

```agda
mul-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos)) =
  m *ℤ m'
pr1 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  n *ℤ n'
pr2 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  is-positive-mul-ℤ n-pos n'-pos

mul-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
mul-fraction-ℤ' x y = mul-fraction-ℤ y x

infixl 40 _*fraction-ℤ_
_*fraction-ℤ_ = mul-fraction-ℤ

ap-mul-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x *fraction-ℤ y ＝ x' *fraction-ℤ y'
ap-mul-fraction-ℤ p q = ap-binary mul-fraction-ℤ p q
```

## Properties

### The multiplication of an integer fraction by zero is similar to zero

```agda
abstract
  left-zero-law-mul-fraction-ℤ :
    (x : fraction-ℤ) → sim-fraction-ℤ (zero-fraction-ℤ *fraction-ℤ x) zero-fraction-ℤ
  left-zero-law-mul-fraction-ℤ _ = refl

  right-zero-law-mul-fraction-ℤ :
    (x : fraction-ℤ) → sim-fraction-ℤ (x *fraction-ℤ zero-fraction-ℤ) zero-fraction-ℤ
  right-zero-law-mul-fraction-ℤ (p , q , _) = equational-reasoning
    (p *ℤ zero-ℤ) *ℤ one-ℤ
    ＝ p *ℤ zero-ℤ by right-unit-law-mul-ℤ (p *ℤ zero-ℤ)
    ＝ zero-ℤ by right-zero-law-mul-ℤ p
```

### Multiplication on integer fractions respects the similarity relation

```agda
sim-fraction-mul-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x *fraction-ℤ y) (x' *fraction-ℤ y')
sim-fraction-mul-fraction-ℤ
  {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
  {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q =
  equational-reasoning
    (nx *ℤ ny) *ℤ (dx' *ℤ dy')
    ＝ (nx *ℤ dx') *ℤ (ny *ℤ dy')
      by interchange-law-mul-mul-ℤ nx ny dx' dy'
    ＝ (nx' *ℤ dx) *ℤ (ny' *ℤ dy)
      by ap-mul-ℤ p q
    ＝ (nx' *ℤ ny') *ℤ (dx *ℤ dy)
      by interchange-law-mul-mul-ℤ nx' dx ny' dy
```

### Unit laws for multiplication on integer fractions

```agda
left-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ one-fraction-ℤ k) k
left-unit-law-mul-fraction-ℤ k = refl

right-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ k one-fraction-ℤ) k
right-unit-law-mul-fraction-ℤ (n , d , p) =
  ap-mul-ℤ (right-unit-law-mul-ℤ n) (inv (right-unit-law-mul-ℤ d))
```

### Multiplication on integer fractions is associative

```agda
associative-mul-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    (mul-fraction-ℤ (mul-fraction-ℤ x y) z)
    (mul-fraction-ℤ x (mul-fraction-ℤ y z))
associative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
  ap-mul-ℤ (associative-mul-ℤ nx ny nz) (inv (associative-mul-ℤ dx dy dz))
```

### Multiplication on integer fractions is commutative

```agda
commutative-mul-fraction-ℤ :
  (x y : fraction-ℤ) → sim-fraction-ℤ (x *fraction-ℤ y) (y *fraction-ℤ x)
commutative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ (commutative-mul-ℤ nx ny) (commutative-mul-ℤ dy dx)
```

### Multiplication on integer fractions distributes over addition

```agda
abstract
  left-distributive-mul-add-fraction-ℤ :
    (x y z : fraction-ℤ) →
    sim-fraction-ℤ
      (mul-fraction-ℤ x (add-fraction-ℤ y z))
      (add-fraction-ℤ (mul-fraction-ℤ x y) (mul-fraction-ℤ x z))
  left-distributive-mul-add-fraction-ℤ
    (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
      ( ap
        ( ( nx *ℤ (ny *ℤ dz +ℤ nz *ℤ dy)) *ℤ_)
        ( ( interchange-law-mul-mul-ℤ dx dy dx dz) ∙
          ( associative-mul-ℤ dx dx (dy *ℤ dz)))) ∙
      ( interchange-law-mul-mul-ℤ
        ( nx)
        ( ny *ℤ dz +ℤ nz *ℤ dy)
        ( dx)
        ( dx *ℤ (dy *ℤ dz))) ∙
      ( inv
        ( associative-mul-ℤ
          ( nx *ℤ dx)
          ( ny *ℤ dz +ℤ nz *ℤ dy)
          ( dx *ℤ (dy *ℤ dz)))) ∙
      ( ap
        ( _*ℤ (dx *ℤ (dy *ℤ dz)))
        ( ( left-distributive-mul-add-ℤ
            ( nx *ℤ dx)
            ( ny *ℤ dz)
            ( nz *ℤ dy)) ∙
          ( ap-add-ℤ
            ( interchange-law-mul-mul-ℤ nx dx ny dz))
            ( interchange-law-mul-mul-ℤ nx dx nz dy)))

  right-distributive-mul-add-fraction-ℤ :
    (x y z : fraction-ℤ) →
    sim-fraction-ℤ
      (mul-fraction-ℤ (add-fraction-ℤ x y) z)
      (add-fraction-ℤ (mul-fraction-ℤ x z) (mul-fraction-ℤ y z))
  right-distributive-mul-add-fraction-ℤ x y z =
    transitive-sim-fraction-ℤ
      ( mul-fraction-ℤ (add-fraction-ℤ x y) z)
      ( mul-fraction-ℤ z (add-fraction-ℤ x y))
      ( add-fraction-ℤ (mul-fraction-ℤ x z) (mul-fraction-ℤ y z))
      ( transitive-sim-fraction-ℤ
        ( mul-fraction-ℤ z (add-fraction-ℤ x y))
        ( add-fraction-ℤ (mul-fraction-ℤ z x) (mul-fraction-ℤ z y))
        ( add-fraction-ℤ (mul-fraction-ℤ x z) (mul-fraction-ℤ y z))
        ( sim-fraction-add-fraction-ℤ
          { mul-fraction-ℤ z x}
          { mul-fraction-ℤ x z}
          { mul-fraction-ℤ z y}
          { mul-fraction-ℤ y z}
          ( commutative-mul-fraction-ℤ z x)
          ( commutative-mul-fraction-ℤ z y))
        ( left-distributive-mul-add-fraction-ℤ z x y))
      ( commutative-mul-fraction-ℤ (add-fraction-ℤ x y) z)

```

### Multiplication by an embedded natural number is repeated addition

```agda
abstract
  mul-nat-iterate-add-fraction-ℤ :
    (n : ℕ) → (x : fraction-ℤ) →
    sim-fraction-ℤ
      ( in-fraction-ℤ (int-ℕ n) *fraction-ℤ x)
      ( iterate n (add-fraction-ℤ x) zero-fraction-ℤ)
  mul-nat-iterate-add-fraction-ℤ zero-ℕ x = left-zero-law-mul-fraction-ℤ x
  mul-nat-iterate-add-fraction-ℤ (succ-ℕ n) x =
    transitive-sim-fraction-ℤ
      ( in-fraction-ℤ (int-ℕ (succ-ℕ n)) *fraction-ℤ x)
      ( x +fraction-ℤ (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
      ( x +fraction-ℤ (iterate n (add-fraction-ℤ x) zero-fraction-ℤ))
      ( sim-fraction-add-fraction-ℤ
        { x}
        { x}
        { in-fraction-ℤ (int-ℕ n) *fraction-ℤ x}
        { iterate n (add-fraction-ℤ x) zero-fraction-ℤ}
        ( refl-sim-fraction-ℤ x)
        ( mul-nat-iterate-add-fraction-ℤ n x))
      (transitive-sim-fraction-ℤ
        (in-fraction-ℤ (int-ℕ (succ-ℕ n)) *fraction-ℤ x)
        ((one-fraction-ℤ +fraction-ℤ in-fraction-ℤ (int-ℕ n)) *fraction-ℤ x)
        (x +fraction-ℤ (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
        (transitive-sim-fraction-ℤ
          ((one-fraction-ℤ +fraction-ℤ in-fraction-ℤ (int-ℕ n)) *fraction-ℤ x)
          ((one-fraction-ℤ *fraction-ℤ x) +fraction-ℤ (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
          (x +fraction-ℤ (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
          (refl)
          (right-distributive-mul-add-fraction-ℤ one-fraction-ℤ (in-fraction-ℤ (int-ℕ n)) x))
        (sim-fraction-mul-fraction-ℤ
          {in-fraction-ℤ (int-ℕ (succ-ℕ n))}
          {one-fraction-ℤ +fraction-ℤ in-fraction-ℤ (int-ℕ n)}
          {x}
          {x}
          (tr
            (λ z → sim-fraction-ℤ z (one-fraction-ℤ +fraction-ℤ in-fraction-ℤ (int-ℕ n)))
            (ap in-fraction-ℤ (inv (left-add-one-ℤ (int-ℕ n)) ∙ succ-int-ℕ n))
            (inv (add-in-fraction-ℤ one-ℤ (int-ℕ n))))
          (refl-sim-fraction-ℤ x)))
```
