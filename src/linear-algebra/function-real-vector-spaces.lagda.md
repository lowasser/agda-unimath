# Function real vector spaces

```agda
module linear-algebra.function-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.dependent-products-real-vector-spaces
open import linear-algebra.real-vector-spaces
```

</details>

## Idea

Given a type `X` and a [real vector space](linear-algebra.real-vector-spaces.md)
`V`, the functions from `X` to `V` form a real vector space.

## Definition

```agda
function-ℝ-Vector-Space :
  {l1 l2 l3 : Level} → UU l1 → ℝ-Vector-Space l2 l3 →
  ℝ-Vector-Space l2 (l1 ⊔ l3)
function-ℝ-Vector-Space X V =
  Π-ℝ-Vector-Space X (λ _ → V)

vector-space-map-ℝ :
  {l1 : Level} (l2 : Level) → UU l1 → ℝ-Vector-Space l2 (l1 ⊔ lsuc l2)
vector-space-map-ℝ l2 X = function-ℝ-Vector-Space X (real-vector-space-ℝ l2)
```
