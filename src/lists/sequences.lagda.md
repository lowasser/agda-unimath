# Sequences

```agda
module lists.sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import lists.dependent-sequences
```

</details>

## Idea

A {{#concept "sequence" WD="infinite sequence" WDID=Q11085785 Agda=sequence}} of
elements of type `A` is a map `ℕ → A` from the
[natural numbers](elementary-number-theory.natural-numbers.md) into `A`.

For a list of number sequences from the
[On-Line Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}
that are formalized in agda-unimath, see the page
[`literature.oeis`](literature.oeis.md).

## Definition

### Sequences of elements of a type

```agda
sequence : {l : Level} → UU l → UU l
sequence A = dependent-sequence (λ _ → A)
```

### The tail of a sequence

```agda
drop-sequence : {l : Level} {A : UU l} → ℕ → sequence A → sequence A
drop-sequence k u = u ∘ add-ℕ' k

tail-sequence : {l : Level} {A : UU l} → sequence A → sequence A
tail-sequence = drop-sequence 1
```

### Functorial action on maps of sequences

```agda
map-sequence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → sequence A → sequence B
map-sequence f a = f ∘ a
```

### Binary functorial action on maps of sequences

```agda
binary-map-sequence :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} → (A → B → C) →
  sequence A → sequence B → sequence C
binary-map-sequence f a b n = f (a n) (b n)
```

### Pairing two sequences

```agda
pair-sequence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → sequence A → sequence B →
  sequence (A × B)
pair-sequence = binary-map-sequence pair
```

## References

{{#bibliography}}
