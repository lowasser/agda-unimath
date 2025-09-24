# Interior inhabited closed intervals in the rational numbers

```agda
module elementary-number-theory.interior-inhabited-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inhabited-closed-intervals-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Given two
[inhabited closed intervals](elementary-number-theory.inhabited-closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) `[a, b]` and
`[c, d]`, `[a, b]` is
{{#concept "interior" disambiguation="closed intervals of rational numbers"}}
to `[c, d]` if `c < a` and `b < d`.

## Definition

```agda
is-interior-to-prop-inhabited-closed-interval-ℚ :
  inhabited-closed-interval-ℚ → inhabited-closed-interval-ℚ → Prop lzero
is-interior-to-prop-inhabited-closed-interval-ℚ ((a , b) , _) ((c , d) , _) =
  le-ℚ-Prop c a ∧ le-ℚ-Prop b d

is-interior-to-inhabited-closed-interval-ℚ :
  inhabited-closed-interval-ℚ → inhabited-closed-interval-ℚ → UU lzero
is-interior-to-inhabited-closed-interval-ℚ [a,b] [c,d] =
  type-Prop (is-interior-to-prop-inhabited-closed-interval-ℚ [a,b] [c,d])
```
