# The action on Cauchy approximations of short maps in pseudometric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

The action of [short maps](metric-spaces.short-maps-pseudometric-spaces.md) on
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) preserves
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Pseudometric-Space l1 l2)
  (Y : Pseudometric-Space l3 l4)
  (f@(map-f , is-short-f) : short-map-Pseudometric-Space X Y)
  (x@(map-x , is-approx-x) : cauchy-approximation-Pseudometric-Space X)
  where

  map-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space :
    ℚ⁺ → type-Pseudometric-Space Y
  map-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space
    ε =
    map-f (map-x ε)

  abstract
    is-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space :
      is-cauchy-approximation-Pseudometric-Space
        ( Y)
        ( map-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space)
    is-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space
      δ ε =
      is-short-f (δ +ℚ⁺ ε) (map-x δ) (map-x ε) (is-approx-x δ ε)

  map-short-map-cauchy-approximation-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space Y
  map-short-map-cauchy-approximation-Pseudometric-Space =
    ( map-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space ,
      is-cauchy-approximation-map-short-map-cauchy-approximation-Pseudometric-Space)
```

## Properties

### Short maps preserve similarity in the Cauchy pseudocompletion of a pseudometric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Pseudometric-Space l1 l2)
  (Y : Pseudometric-Space l3 l4)
  (f@(map-f , is-short-f) : short-map-Pseudometric-Space X Y)
  where abstract

  preserves-sim-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    preserves-sim-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Pseudometric-Space X)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Pseudometric-Space Y)
      ( map-short-map-cauchy-approximation-Pseudometric-Space X Y f)
  preserves-sim-short-map-cauchy-pseudocompletion-Pseudometric-Space
    {x , is-approx-x} {y , is-approx-y} x~y δ ε θ =
    is-short-f (ε +ℚ⁺ θ +ℚ⁺ δ) (x ε) (y θ) (x~y δ ε θ)
```
