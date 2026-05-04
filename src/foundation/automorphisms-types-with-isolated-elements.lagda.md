# Automorphisms of types with isolated elements

```agda
module foundation.automorphisms-types-with-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-types-with-isolated-elements
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.retractions
open import foundation.sections
open import foundation.transpositions-isolated-elements
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
```

</details>

## Idea

Consider a type `A` equipped with an
[isolated element](foundation.isolated-elements.md) `a`, and write `C` for the
complement of `a` in `A`. Then there is an
[equivalence](foundation-core.equivalences.md)

```text
  Aut A ≃ Aut C × isolated-element A.
```

The idea behind the proof is that every automorphism `e` on A can be factored as
an equivalence that fixes the point `a` and the
[transposition](foundation.transpositions-types-with-isolated-elements.md) with
the isolated element `b := e a`. By this unique factorization result, we obtain
an equivalence

```text
  Aut A ≃ ((A , a) ≃∗ (A , a)) × isolated-element A.
```

The proof is then finished by showing that any equivalence that fixes the
isolated element `a` is uniquely determined by an automorphism on the complement
of `a`.

## Definitions

### The value of an automorphism at an isolated element, and the transposition associated to it

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  value-aut-isolated-element :
    (e : A ≃ A) → isolated-element A
  value-aut-isolated-element e = map-equiv-isolated-element e (a , d)

  transposition-value-aut-isolated-element :
    (e : A ≃ A) → A ≃ A
  transposition-value-aut-isolated-element e =
    transposition-isolated-elements (a , d) (value-aut-isolated-element e)

  aut-pointed-aut-isolated-element :
    (e : A ≃ A) → A ≃ A
  aut-pointed-aut-isolated-element e =
    transposition-value-aut-isolated-element e ∘e e

  map-pointed-aut-isolated-element :
    (e : A ≃ A) → A → A
  map-pointed-aut-isolated-element e =
    map-equiv (aut-pointed-aut-isolated-element e)

  preserves-point-pointed-aut-isolated-element :
    (e : A ≃ A) → map-pointed-aut-isolated-element e a ＝ a
  preserves-point-pointed-aut-isolated-element e =
    compute-second-value-transposition-isolated-elements
      ( a , d)
      ( value-aut-isolated-element e)

  pointed-aut-isolated-element :
    (e : A ≃ A) → (A , a) ≃∗ (A , a)
  pr1 (pointed-aut-isolated-element e) =
    aut-pointed-aut-isolated-element e
  pr2 (pointed-aut-isolated-element e) =
    preserves-point-pointed-aut-isolated-element e

  decomposition-aut-isolated-element :
    (e : A ≃ A) → ((A , a) ≃∗ (A , a)) × isolated-element A
  pr1 (decomposition-aut-isolated-element e) =
    pointed-aut-isolated-element e
  pr2 (decomposition-aut-isolated-element e) =
    value-aut-isolated-element e

  composition-aut-isolated-element :
    ((A , a) ≃∗ (A , a)) × isolated-element A → A ≃ A
  composition-aut-isolated-element ((h , p) , b) =
    transposition-isolated-elements (a , d) b ∘e h
```

### Any equivalence that fixes an isolated point is uniquely determined by its restriction to the complement

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  ((e , p) (f , q) : (A , a) ≃∗ (A , a))
  where

  htpy-equiv-complement-isolated-element :
    map-equiv-complement-isolated-element e (a , d) (a , d) p ~
    map-equiv-complement-isolated-element f (a , d) (a , d) q →
    htpy-equiv e f
  htpy-equiv-complement-isolated-element H x =
    rec-coproduct
      ( λ { refl → p ∙ inv q})
      ( λ n → ap pr1 (H (x , n)))
      ( d x)
```
