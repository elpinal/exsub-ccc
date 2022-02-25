module Categories.Functor.Construction.Exponential where

open import Categories.Category
open import Categories.Category.Product using (Product)
open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Object.Exponential
open import Categories.Functor.Bifunctor

open import Data.Product using (_,_; proj₁; proj₂)

module _ {o ℓ e} (𝒞 : Category o ℓ e) (cartesianClosed : CartesianClosed 𝒞) where
  open import Categories.Morphism.Reasoning 𝒞

  open CartesianClosed cartesianClosed
  open Cartesian cartesian
  open BinaryProducts products

  open Category 𝒞
  open Equiv

  private
    P : Category _ _ _
    P = Product 𝒞 op

  Exp : Bifunctor 𝒞 (Category.op 𝒞) 𝒞
  Exp = record
              { F₀ = λ (x , y) → x ^ y
              ; F₁ = λ (f , g) → λg (f ∘ eval′ ∘ (id ⁂ g))
              ; identity = λ {A} →
                  begin
                    λg (id ∘ eval′ ∘ (id ⁂ id))
                  ≈⟨ λ-cong identityˡ ⟩
                    λg (eval′ ∘ (id ⁂ id))
                  ≈⟨ λ-cong (elimʳ (Equiv.trans (⟨⟩-cong₂ identityˡ identityˡ) η)) ⟩
                    λg eval′
                  ≈⟨ η-id′ ⟩
                    id
                  ∎
              ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                  begin
                    λg ((proj₁ g ∘ proj₁ f) ∘ eval′ ∘ (id ⁂ (proj₂ f ∘ proj₂ g)))
                  ≈⟨ λ-cong assoc ⟩
                    λg (proj₁ g ∘ proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f ∘ proj₂ g))
                  ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (trans ⁂∘⁂ (⁂-cong₂ identity² refl))))) ⟩
                    λg (proj₁ g ∘ proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f) ∘ (id ⁂ proj₂ g))
                  ≈˘⟨ λ-cong (∘-resp-≈ʳ assoc²') ⟩
                    λg (proj₁ g ∘ (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ∘ (id ⁂ proj₂ g))
                  ≈˘⟨ λ-cong (∘-resp-≈ʳ (pullˡ β′)) ⟩
                    λg (proj₁ g ∘ eval′ ∘ (λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ⁂ id) ∘ (id ⁂ proj₂ g))
                  ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
                    λg (proj₁ g ∘ eval′ ∘ (λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ∘ id ⁂ id ∘ proj₂ g))
                  ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ (trans identityʳ (sym identityˡ)) (trans identityˡ (sym identityʳ))))) ⟩
                    λg (proj₁ g ∘ eval′ ∘ (id ∘ λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ⁂ proj₂ g ∘ id))
                  ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
                    λg (proj₁ g ∘ eval′ ∘ (id ⁂ proj₂ g) ∘ (λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ⁂ id))
                  ≈˘⟨ λ-cong assoc²' ⟩
                    λg ((proj₁ g ∘ eval′ ∘ (id ⁂ proj₂ g)) ∘ (λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f)) ⁂ id))
                  ≈˘⟨ exp.subst product product ⟩
                    λg (proj₁ g ∘ eval′ ∘ (id ⁂ proj₂ g)) ∘ λg (proj₁ f ∘ eval′ ∘ (id ⁂ proj₂ f))
                  ∎
              ; F-resp-≈ = λ (x , y) → λ-cong (∘-resp-≈ x (∘-resp-≈ʳ (⁂-cong₂ Equiv.refl y)))
              }
    where open HomReasoning
