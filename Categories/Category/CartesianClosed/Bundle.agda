module Categories.Category.CartesianClosed.Bundle where

open import Categories.Category using (Category)
open import Categories.Category.CartesianClosed using (CartesianClosed)

open import Level

record CartesianClosedCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U : Category o ℓ e
    cartesianClosed : CartesianClosed U

  open Category U public
  open CartesianClosed cartesianClosed public
