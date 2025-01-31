# The group of integers

```agda
module elementary-number-theory.group-of-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.multiples-of-elements-abelian-groups
open import group-theory.semigroups
```

</details>

## Idea

The type of integers, equipped with a zero-element, addition, and negatives,
forms a group.

## Definition

```agda
ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ

ℤ-Ab : Ab lzero
pr1 ℤ-Ab = ℤ-Group
pr2 ℤ-Ab = commutative-add-ℤ
```

### Multiplication by a natural number agrees with Abelian group multiplication

```agda
mul-nat-multiple-Ab-ℤ :
  (n : ℕ) (x : ℤ) → int-ℕ n *ℤ x ＝ multiple-Ab ℤ-Ab n x
mul-nat-multiple-Ab-ℤ zero-ℕ x = refl
mul-nat-multiple-Ab-ℤ (succ-ℕ zero-ℕ) x = left-unit-law-mul-ℤ x
mul-nat-multiple-Ab-ℤ (succ-ℕ (succ-ℕ n)) x = equational-reasoning
  int-ℕ (succ-ℕ (succ-ℕ n)) *ℤ x
  ＝ succ-ℤ (int-ℕ (succ-ℕ n)) *ℤ x
    by ap (_*ℤ x) (inv (succ-int-ℕ (succ-ℕ n)))
  ＝ x +ℤ (int-ℕ (succ-ℕ n) *ℤ x)
    by left-successor-law-mul-ℤ (int-ℕ (succ-ℕ n)) x
  ＝ (int-ℕ (succ-ℕ n) *ℤ x) +ℤ x
    by commutative-add-ℤ x (int-ℕ (succ-ℕ n) *ℤ x)
  ＝ multiple-Ab ℤ-Ab (succ-ℕ n) x +ℤ x
    by ap (_+ℤ x) (mul-nat-multiple-Ab-ℤ (succ-ℕ n) x)
```
