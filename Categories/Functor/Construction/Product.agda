module Categories.Functor.Construction.Product where

open import Categories.Category
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Functor.Bifunctor

open import Data.Product using (_,_)

module _ {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where
  open Cartesian cartesian
  open BinaryProducts products

  open Category 𝒞

  Product : Bifunctor 𝒞 𝒞 𝒞
  Product = record
              { F₀ = λ (x , y) → x × y
              ; F₁ = λ (f , g) → f ⁂ g
              ; identity = Equiv.trans (⟨⟩-cong₂ identityˡ identityˡ) η
              ; homomorphism = Equiv.sym ⁂∘⁂
              ; F-resp-≈ = λ (x , y) → ⁂-cong₂ x y
              }
