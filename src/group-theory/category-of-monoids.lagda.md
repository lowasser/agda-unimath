# The category of monoids

```agda
module group-theory.category-of-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories

open import foundation.1-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.isomorphisms-monoids
open import group-theory.monoids
open import group-theory.precategory-of-monoids
```

</details>

## Definitions

```agda
is-large-category-Monoid :
  is-large-category-Large-Precategory Monoid-Large-Precategory
is-large-category-Monoid M =
  fundamental-theorem-id (is-torsorial-iso-Monoid M) (iso-eq-Monoid M)

eq-iso-Monoid : {l : Level} (M N : Monoid l) → iso-Monoid M N → Id M N
eq-iso-Monoid M N = map-inv-is-equiv (is-large-category-Monoid M N)

Monoid-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Monoid-Large-Category =
  Monoid-Large-Precategory
is-large-category-Large-Category Monoid-Large-Category =
  is-large-category-Monoid

Monoid-Category : (l : Level) → Category (lsuc l) l
Monoid-Category = category-Large-Category Monoid-Large-Category
```

## Corollaries

### The type of monoids is a 1-type

```agda
is-1-type-Monoid : {l : Level} → is-1-type (Monoid l)
is-1-type-Monoid {l} = is-1-type-obj-Category (Monoid-Category l)
```
