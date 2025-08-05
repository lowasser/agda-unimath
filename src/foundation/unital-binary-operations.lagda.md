# Unital binary operations

```agda
module foundation.unital-binary-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A binary operation of type `A → A → A` is **unital** if there is a unit of type
`A` that satisfies both the left and right unit laws. Furthermore, a binary
operation is **coherently unital** if the proofs of the left and right unit laws
agree on the case where both arguments of the operation are the unit.

## Definitions

### Unit laws

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) (e : A)
  where

  left-unit-law : UU l
  left-unit-law = (x : A) → μ e x ＝ x

  right-unit-law : UU l
  right-unit-law = (x : A) → μ x e ＝ x

  coh-unit-laws : left-unit-law → right-unit-law → UU l
  coh-unit-laws α β = (α e ＝ β e)

  unit-laws : UU l
  unit-laws = left-unit-law × right-unit-law

  coherent-unit-laws : UU l
  coherent-unit-laws =
    Σ left-unit-law (λ α → Σ right-unit-law (coh-unit-laws α))

is-prop-left-unit-law-Set :
  {l : Level} (A : Set l) (μ : type-Set A → type-Set A → type-Set A) →
  (e : type-Set A) → is-prop (left-unit-law μ e)
is-prop-left-unit-law-Set A μ e =
  is-prop-Π (λ a → is-set-type-Set A (μ e a) a)

is-prop-right-unit-law-Set :
  {l : Level} (A : Set l) (μ : type-Set A → type-Set A → type-Set A) →
  (e : type-Set A) → is-prop (right-unit-law μ e)
is-prop-right-unit-law-Set A μ e =
  is-prop-Π (λ a → is-set-type-Set A (μ a e) a)

is-prop-unit-laws-Set :
  {l : Level} (A : Set l) (μ : type-Set A → type-Set A → type-Set A) →
  (e : type-Set A) → is-prop (unit-laws μ e)
is-prop-unit-laws-Set A μ e =
  is-prop-product
    ( is-prop-left-unit-law-Set A μ e)
    ( is-prop-right-unit-law-Set A μ e)
```

### Unital binary operations

```agda
is-unital : {l : Level} {A : UU l} (μ : A → A → A) → UU l
is-unital {A = A} μ = Σ A (unit-laws μ)

is-prop-is-unital-Set :
  {l : Level} (A : Set l) (μ : type-Set A → type-Set A → type-Set A) →
  is-prop (is-unital μ)
is-prop-is-unital-Set A μ =
  is-prop-all-elements-equal
    ( λ (a , unit-a) (b , unit-b) →
      eq-pair-Σ
        ( inv (pr1 unit-b a) ∙ pr2 unit-a b)
        ( eq-type-Prop (unit-laws μ b , is-prop-unit-laws-Set A μ b)))

is-unital-prop-Set :
  {l : Level} (A : Set l) (μ : type-Set A → type-Set A → type-Set A) →
  Prop l
is-unital-prop-Set A μ = (is-unital μ , is-prop-is-unital-Set A μ)
```

### Coherently unital binary operations

```agda
is-coherently-unital : {l : Level} {A : UU l} (μ : A → A → A) → UU l
is-coherently-unital {A = A} μ = Σ A (coherent-unit-laws μ)
```

## Properties

### The unit laws for an operation `μ` with unit `e` can be upgraded to coherent unit laws

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) {e : A}
  where

  coherent-unit-laws-unit-laws : unit-laws μ e → coherent-unit-laws μ e
  pr1 (coherent-unit-laws-unit-laws (pair H K)) = H
  pr1 (pr2 (coherent-unit-laws-unit-laws (pair H K))) x =
    ( inv (ap (μ x) (K e))) ∙ (( ap (μ x) (H e)) ∙ (K x))
  pr2 (pr2 (coherent-unit-laws-unit-laws (pair H K))) =
    left-transpose-eq-concat
      ( ap (μ e) (K e))
      ( H e)
      ( (ap (μ e) (H e)) ∙ (K e))
      ( ( inv-nat-htpy-id (H) (K e)) ∙
        ( right-whisker-concat (coh-htpy-id (H) e) (K e)))

module _
  {l : Level} {A : UU l} {μ : A → A → A}
  where

  is-coherently-unital-is-unital : is-unital μ → is-coherently-unital μ
  pr1 (is-coherently-unital-is-unital (pair e H)) = e
  pr2 (is-coherently-unital-is-unital (pair e H)) =
    coherent-unit-laws-unit-laws μ H
```
