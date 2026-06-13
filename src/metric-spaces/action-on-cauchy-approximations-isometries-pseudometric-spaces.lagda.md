# The action on Cauchy approximations of isometries in pseudometric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

[Isometries](metric-spaces.isometries-pseudometric-spaces.md) on
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) induce isometries on
the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md)
of the pseudometric spaces.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Pseudometric-Space l1 l2)
  (Y : Pseudometric-Space l3 l4)
  (f : isometry-Pseudometric-Space X Y)
  where

  map-isometry-cauchy-approximation-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space X →
    cauchy-approximation-Pseudometric-Space Y
  map-isometry-cauchy-approximation-Pseudometric-Space =
    map-short-map-cauchy-approximation-Pseudometric-Space
      ( X)
      ( Y)
      ( short-map-isometry-Pseudometric-Space X Y f)
```

## Properties

### Mapping an isometry on Cauchy approximations in a pseudometric space is an isometry in the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Pseudometric-Space l1 l2)
  (Y : Pseudometric-Space l3 l4)
  (f : isometry-Pseudometric-Space X Y)
  where

  abstract
    is-isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space :
      is-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space X)
        ( cauchy-pseudocompletion-Pseudometric-Space Y)
        ( map-isometry-cauchy-approximation-Pseudometric-Space X Y f)
    pr1
      ( is-isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space
        d (x , is-approx-x) (y , is-approx-y))
      Ndxy δ ε =
      preserves-neighborhoods-map-isometry-Pseudometric-Space
        ( X)
        ( Y)
        ( f)
        ( δ +ℚ⁺ ε +ℚ⁺ d)
        ( x δ)
        ( y ε)
        ( Ndxy δ ε)
    pr2
      ( is-isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space
        d (x , is-approx-x) (y , is-approx-y))
      Ndfxfy δ ε =
      reflects-neighborhoods-map-isometry-Pseudometric-Space
        ( X)
        ( Y)
        ( f)
        ( δ +ℚ⁺ ε +ℚ⁺ d)
        ( x δ)
        ( y ε)
        ( Ndfxfy δ ε)

  isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space X)
      ( cauchy-pseudocompletion-Pseudometric-Space Y)
  isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space =
    ( map-isometry-cauchy-approximation-Pseudometric-Space X Y f ,
      is-isometry-cauchy-pseudocompletion-isometry-Pseudometric-Space)
```
