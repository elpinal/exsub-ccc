module Categories.Category.Construction.CartesianClosedFunctors where

open import Categories.Category
open import Categories.Category.CartesianClosed.Bundle
open import Categories.Functor.CartesianClosed
open import Categories.NaturalTransformation using (NaturalTransformation; id; _∘ᵥ_)
import Categories.NaturalTransformation.Equivalence as NTEq
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.NaturalTransformation.NaturalIsomorphism.Equivalence as Eq

open import Data.Product using (_,_)

open import Level

private
  variable o ℓ e o′ ℓ′ e′ : Level

CCCat≅ : (C : CartesianClosedCategory o ℓ e)
  -> (D : CartesianClosedCategory o′ ℓ′ e′)
  -> Category (levelOfTerm C ⊔ levelOfTerm D) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
CCCat≅ C D = record
               { Obj = CartesianClosedF C D
               ; _⇒_ = λ F G → NaturalIsomorphism (CartesianClosedF.F F) (CartesianClosedF.F G)
               ; _≈_ = Eq._≅_
               ; id = refl
               ; _∘_ = _ⓘᵥ_
               ; assoc = assoc , sym-assoc
               ; sym-assoc = sym-assoc , assoc
               ; identityˡ = identityˡ , identityʳ
               ; identityʳ = identityʳ , identityˡ
               ; identity² = identity² , identity²
               ; equiv = Eq.≅-isEquivalence
               ; ∘-resp-≈ = λ (f≅h , f≅h′) (g≅i , g≅i′) → ∘-resp-≈ f≅h g≅i , ∘-resp-≈ g≅i′ f≅h′
               }
  where
    open Category (CartesianClosedCategory.U D)
