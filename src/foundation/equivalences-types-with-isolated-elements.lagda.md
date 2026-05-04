# Equivalences between types with isolated elements

```agda
module foundation.equivalences-types-with-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.logical-equivalences
open import foundation-core.subtypes

open import structured-types.pointed-equivalences
```

</details>

## Idea

Consider an [equivalence](foundation-core.equivalences.md) `e : A ≃ B`. Then `e`
maps [isolated elements](foundation.isolated-elements.md) in `A` to isolated
elements in `B`. This way, the equivalence `e` induces an equivalence

```text
  isolated-element A ≃ isolated-element B.
```

## Definitions

### Functoriality of `isolated-element`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  abstract
    preserves-isolated-elements-equiv :
      {a : A} → is-isolated a → is-isolated (map-equiv e a)
    preserves-isolated-elements-equiv d y =
      map-coproduct
        ( λ p → ap (map-equiv e) p ∙ is-section-map-inv-equiv e y)
        ( λ f → f ∘ map-eq-transpose-equiv e)
        ( d (map-inv-equiv e y))

  abstract
    reflects-isolated-elements-equiv :
      {a : A} → is-isolated (map-equiv e a) → is-isolated a
    reflects-isolated-elements-equiv d x =
      map-coproduct
        ( is-injective-equiv e)
        ( λ f → f ∘ ap (map-equiv e))
        ( d (map-equiv e x))

  preserves-and-reflects-isolated-elements-equiv :
    (a : A) → is-isolated a ↔ is-isolated (map-equiv e a)
  pr1 (preserves-and-reflects-isolated-elements-equiv a) =
    preserves-isolated-elements-equiv
  pr2 (preserves-and-reflects-isolated-elements-equiv a) =
    reflects-isolated-elements-equiv

  equiv-isolated-element :
    isolated-element A ≃ isolated-element B
  equiv-isolated-element =
    equiv-subtype-equiv e
      ( is-isolated-Prop)
      ( is-isolated-Prop)
      ( preserves-and-reflects-isolated-elements-equiv)

  map-equiv-isolated-element :
    isolated-element A → isolated-element B
  map-equiv-isolated-element =
    map-equiv equiv-isolated-element
```

### Functoriality of the complement of an isolated element

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  ((e , p) : (A , a) ≃∗ (B , b))
  where

  equiv-complement-isolated-element :
    complement-isolated-element (a , d) ≃ complement-isolated-element (b , c)
  equiv-complement-isolated-element =
    equiv-Σ
      ( is-in-complement-isolated-element (b , c))
      ( e)
      ( λ x →
        equiv-neg
          ( equiv-concat (inv p) (map-equiv e x) ∘e
            equiv-ap e (element-isolated-element (a , d)) x))

  map-equiv-complement-isolated-element :
    complement-isolated-element (a , d) → complement-isolated-element (b , c)
  map-equiv-complement-isolated-element =
    map-equiv equiv-complement-isolated-element

  natural-inclusion-equiv-complement-isolated-element :
    coherence-square-maps
      ( inclusion-complement-isolated-element (a , d))
      ( map-equiv equiv-complement-isolated-element)
      ( map-equiv e)
      ( inclusion-complement-isolated-element (b , c))
  natural-inclusion-equiv-complement-isolated-element (x , f) = refl
```

## Properties

### A pointed equivalence pointed at isolated elements is equivalently described by the induced equivalence on the complements

We note that equality of equivalences between types with isolated base points is equivalent to [homotopies](foundation-core.homotopies.md) between them. Since preserving the base point is a property, it is unnecessary to consider [pointed homotopies](structured-types.pointed-homotopies.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  where

  htpy-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) → UU (l1 ⊔ l2)
  htpy-pointed-equiv-isolated-element e f =
    map-pointed-equiv e ~ map-pointed-equiv f

  refl-htpy-pointed-equiv-isolated-element :
    (e : (A , a) ≃∗ (B , b)) → htpy-pointed-equiv-isolated-element e e
  refl-htpy-pointed-equiv-isolated-element e =
    refl-htpy

  htpy-eq-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) →
    e ＝ f → htpy-pointed-equiv-isolated-element e f
  htpy-eq-pointed-equiv-isolated-element e f refl =
    refl-htpy-pointed-equiv-isolated-element e

  is-torsorial-htpy-pointed-equiv-isolated-element :
    (e : (A , a) ≃∗ (B , b)) →
    is-torsorial (htpy-pointed-equiv-isolated-element e)
  is-torsorial-htpy-pointed-equiv-isolated-element (e , p) =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy-equiv e)
      ( λ f →
        is-prop-eq-isolated-element
          ( map-equiv f a)
          ( preserves-isolated-elements-equiv f d)
          ( b))
      ( e)
      ( refl-htpy)
      ( p)
```
