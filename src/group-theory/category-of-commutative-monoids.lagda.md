# The category of commutative monoids

```agda
module group-theory.category-of-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.full-large-subcategories
open import category-theory.functors-large-categories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import group-theory.category-of-monoids
open import group-theory.commutative-monoids
```

</details>

## Idea

The **category of commutative monoids** is the
[full large subcategory](category-theory.full-large-subcategories.md) of the
[category of monoids](group-theory.category-of-monoids.md) consisting of
[monoids](group-theory.monoids.md) of which the monoid operation is
[commutative](group-theory.commutative-monoids.md).

## Definitions

### The large category of commutative monoids

```agda
Commutative-Monoid-Large-Category : Large-Category lsuc (_⊔_)
Commutative-Monoid-Large-Category =
  large-category-Full-Large-Subcategory
    ( Monoid-Large-Category)
    ( is-commutative-prop-Monoid)
```

### The large precategory of commutative monoids

```agda
Commutative-Monoid-Large-Precategory : Large-Precategory lsuc (_⊔_)
Commutative-Monoid-Large-Precategory =
  large-precategory-Large-Category Commutative-Monoid-Large-Category
```

### The category of commutative monoids of a given universe level

```agda
Commutative-Monoid-Category : (l : Level) → Category (lsuc l) l
Commutative-Monoid-Category =
  category-Large-Category Commutative-Monoid-Large-Category
```

### The precategory of commutative monoids of a given universe level

```agda
Commutative-Monoid-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Monoid-Precategory =
  precategory-Large-Category Commutative-Monoid-Large-Category
```

### The forgetful functor from commutative monoids to monoids

```agda
forgetful-functor-Commutative-Monoid :
  functor-Large-Category
    ( λ l → l)
    ( Commutative-Monoid-Large-Category)
    ( Monoid-Large-Category)
forgetful-functor-Commutative-Monoid =
  forgetful-functor-Full-Large-Subcategory
    ( Monoid-Large-Category)
    ( is-commutative-prop-Monoid)
```
