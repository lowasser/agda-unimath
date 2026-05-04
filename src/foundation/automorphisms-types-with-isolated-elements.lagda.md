# Automorphisms of types with isolated elements

```agda
module foundation.automorphisms-types-with-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-types-with-isolated-elements
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transpositions-isolated-elements
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

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

### The type of decompositions of automorphisms on types with isolated elements

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  decomposition-aut-isolated-element : UU l1
  decomposition-aut-isolated-element =
    ((A , a) ≃∗ (A , a)) × isolated-element A

  pointed-aut-decomposition-aut-isolated-element :
    decomposition-aut-isolated-element → (A , a) ≃∗ (A , a)
  pointed-aut-decomposition-aut-isolated-element = pr1

  aut-decomposition-aut-isolated-element :
    decomposition-aut-isolated-element → Aut A
  aut-decomposition-aut-isolated-element e =
    equiv-pointed-equiv (pointed-aut-decomposition-aut-isolated-element e)

  isolated-element-decomposition-aut-isolated-element :
    decomposition-aut-isolated-element → isolated-element A
  isolated-element-decomposition-aut-isolated-element = pr2

  element-decomposition-aut-isolated-element :
    decomposition-aut-isolated-element → A
  element-decomposition-aut-isolated-element e =
    element-isolated-element
      ( isolated-element-decomposition-aut-isolated-element e)

  htpy-decomposition-aut-isolated-element :
    (e f : decomposition-aut-isolated-element) → UU l1
  htpy-decomposition-aut-isolated-element (e , b) (f , c) =
    ( htpy-pointed-equiv e f) ×
    ( element-isolated-element b ＝ element-isolated-element c)

  refl-htpy-decomposition-aut-isolated-element :
    (e : decomposition-aut-isolated-element) →
    htpy-decomposition-aut-isolated-element e e
  refl-htpy-decomposition-aut-isolated-element (e , b) =
    ( refl-htpy , refl)

  htpy-eq-decomposition-aut-isolated-element :
    (e f : decomposition-aut-isolated-element) →
    e ＝ f → htpy-decomposition-aut-isolated-element e f
  htpy-eq-decomposition-aut-isolated-element e f refl =
    refl-htpy-decomposition-aut-isolated-element e

  is-torsorial-htpy-decomposition-aut-isolated-element :
    (e : decomposition-aut-isolated-element) →
    is-torsorial (htpy-decomposition-aut-isolated-element e)
  is-torsorial-htpy-decomposition-aut-isolated-element ((e , p) , b) =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-subtype
        ( is-torsorial-htpy-equiv e)
        ( λ f →
          is-prop-eq-isolated-element _
            ( preserves-isolated-elements-equiv f d)
            ( a))
        ( e)
        ( refl-htpy)
        ( p))
      ( (e , p) , refl-htpy)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-Id _)
        ( is-prop-is-isolated)
        ( element-isolated-element b)
        ( refl)
        ( is-isolated-isolated-element b))

  is-equiv-htpy-eq-decomposition-aut-isolated-element :
    (e f : decomposition-aut-isolated-element) →
    is-equiv (htpy-eq-decomposition-aut-isolated-element e f)
  is-equiv-htpy-eq-decomposition-aut-isolated-element e =
    fundamental-theorem-id
      ( is-torsorial-htpy-decomposition-aut-isolated-element e)
      ( htpy-eq-decomposition-aut-isolated-element e)

  extensionality-decomposition-aut-isolated-element :
    (e f : decomposition-aut-isolated-element) →
    (e ＝ f) ≃ htpy-decomposition-aut-isolated-element e f
  pr1 (extensionality-decomposition-aut-isolated-element e f) =
    htpy-eq-decomposition-aut-isolated-element e f
  pr2 (extensionality-decomposition-aut-isolated-element e f) =
    is-equiv-htpy-eq-decomposition-aut-isolated-element e f

  eq-htpy-decomposition-aut-isolated-element :
    ((e , b) (f , c) : decomposition-aut-isolated-element) →
    htpy-pointed-equiv e f →
    element-isolated-element b ＝ element-isolated-element c →
    (e , b) ＝ (f , c)
  eq-htpy-decomposition-aut-isolated-element e f H p =
    map-inv-equiv
      ( extensionality-decomposition-aut-isolated-element e f)
      ( H , p)
```

### The value of an automorphism at an isolated element, and the transposition associated to it

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  value-aut-isolated-element :
    Aut A → isolated-element A
  value-aut-isolated-element e = map-equiv-isolated-element e (a , d)

  transposition-value-aut-isolated-element :
    Aut A → Aut A
  transposition-value-aut-isolated-element e =
    transposition-isolated-elements (a , d) (value-aut-isolated-element e)

  aut-pointed-aut-isolated-element :
    Aut A → Aut A
  aut-pointed-aut-isolated-element e =
    transposition-value-aut-isolated-element e ∘e e

  map-pointed-aut-isolated-element :
    Aut A → A → A
  map-pointed-aut-isolated-element e =
    map-equiv (aut-pointed-aut-isolated-element e)

  preserves-point-pointed-aut-isolated-element :
    (e : Aut A) → map-pointed-aut-isolated-element e a ＝ a
  preserves-point-pointed-aut-isolated-element e =
    compute-second-value-transposition-isolated-elements
      ( a , d)
      ( value-aut-isolated-element e)

  pointed-aut-isolated-element :
    Aut A → (A , a) ≃∗ (A , a)
  pr1 (pointed-aut-isolated-element e) =
    aut-pointed-aut-isolated-element e
  pr2 (pointed-aut-isolated-element e) =
    preserves-point-pointed-aut-isolated-element e

  decomposition-aut-aut-isolated-element :
    Aut A → ((A , a) ≃∗ (A , a)) × isolated-element A
  pr1 (decomposition-aut-aut-isolated-element e) =
    pointed-aut-isolated-element e
  pr2 (decomposition-aut-aut-isolated-element e) =
    value-aut-isolated-element e

  composition-aut-aut-isolated-element :
    ((A , a) ≃∗ (A , a)) × isolated-element A → Aut A
  composition-aut-aut-isolated-element ((h , p) , b) =
    transposition-isolated-elements (a , d) b ∘e h

  eq-isolated-element-is-section-composition-aut-aut-isolated-element :
    (((e , p) , b) : decomposition-aut-isolated-element (a , d)) →
    element-decomposition-aut-isolated-element
      ( a , d)
      ( decomposition-aut-aut-isolated-element
          ( composition-aut-aut-isolated-element ((e , p) , b))) ＝
    element-isolated-element b
  eq-isolated-element-is-section-composition-aut-aut-isolated-element
    ((e , p) , b) =
    ap (map-transposition-isolated-elements (a , d) b) p ∙
    compute-first-value-transposition-isolated-elements (a , d) b

  htpy-is-section-composition-aut-aut-isolated-element :
    (((e , p) , b) : decomposition-aut-isolated-element (a , d)) →
    htpy-equiv
      ( aut-decomposition-aut-isolated-element
        ( a , d)
        ( decomposition-aut-aut-isolated-element
          ( composition-aut-aut-isolated-element ((e , p) , b))))
      ( e)
  htpy-is-section-composition-aut-aut-isolated-element ((e , p) , b) =
    right-whisker-comp
      ( htpy-transposition-isolated-elements
        ( a , d)
        ( a , d)
        ( isolated-element-decomposition-aut-isolated-element
          ( a , d)
          ( decomposition-aut-aut-isolated-element
            ( composition-aut-aut-isolated-element ((e , p) , b))))
        ( b)
        ( refl)
        ( eq-isolated-element-is-section-composition-aut-aut-isolated-element
          ( (e , p) , b)))
      ( map-equiv
        ( composition-aut-aut-isolated-element ((e , p) , b))) ∙h
    right-whisker-comp
      ( is-involution-transposition-isolated-elements (a , d) b)
      ( map-equiv e)

  is-section-composition-aut-aut-isolated-element :
    is-section
      decomposition-aut-aut-isolated-element
      composition-aut-aut-isolated-element
  is-section-composition-aut-aut-isolated-element e =
    eq-htpy-decomposition-aut-isolated-element
      ( a , d)
      ( decomposition-aut-aut-isolated-element
        ( composition-aut-aut-isolated-element e))
      ( e)
      ( htpy-is-section-composition-aut-aut-isolated-element e)
      ( eq-isolated-element-is-section-composition-aut-aut-isolated-element e)

  is-retraction-composition-aut-aut-isolated-element :
    is-retraction
      decomposition-aut-aut-isolated-element
      composition-aut-aut-isolated-element
  is-retraction-composition-aut-aut-isolated-element e =
    eq-htpy-equiv
      ( right-whisker-comp
        ( is-involution-transposition-isolated-elements
          ( a , d)
          ( value-aut-isolated-element e))
        ( map-equiv e))

  is-equiv-decomposition-aut-aut-isolated-element :
    is-equiv decomposition-aut-aut-isolated-element
  is-equiv-decomposition-aut-aut-isolated-element =
    is-equiv-is-invertible
      composition-aut-aut-isolated-element
      is-section-composition-aut-aut-isolated-element
      is-retraction-composition-aut-aut-isolated-element

  equiv-decomposition-aut-aut-isolated-element :
    Aut A ≃ decomposition-aut-isolated-element (a , d)
  pr1 equiv-decomposition-aut-aut-isolated-element =
    decomposition-aut-aut-isolated-element
  pr2 equiv-decomposition-aut-aut-isolated-element =
    is-equiv-decomposition-aut-aut-isolated-element
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
