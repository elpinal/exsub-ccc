open import Theory
open import Categories.Category using (Category)
open import Categories.Category.CartesianClosed

module Soundness {o ℓ e}
  (𝒞 : Category o ℓ e)
  (CC : CartesianClosed 𝒞)
  {ℓ₁ ℓ₂ ℓ₃}
  (Th : Theory ℓ₁ ℓ₂ ℓ₃)
  where

  open Theory.Theory Th
  open import Semantics 𝒞 CC Sg
  open import Syntax
  open Term Sg

  open import Categories.Category.Cartesian 𝒞
  open import Categories.Category.BinaryProducts 𝒞
  open import Categories.Object.Product 𝒞

  open Category 𝒞
  open CartesianClosed CC
  open Cartesian cartesian
  open BinaryProducts products

  open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)

  module _ (M : Model 𝒞 CC Th) where
    open Structure (proj₁ M)
    open HomReasoning

    soundness : forall {Γ A} {e₁ e₂ : Γ ⊢ A}
      -> Γ ⊢ e₁ ≡ e₂
      -> ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
    soundness-sub : forall {Γ Γ′} {γ₁ γ₂ : Γ ⊨ Γ′}
      -> Γ ⊨ γ₁ ≡ γ₂
      -> ⟦ γ₁ ⟧S ≈ ⟦ γ₂ ⟧S

    soundness (ax x) = proj₂ M x
    soundness refl = Equiv.refl
    soundness (sym D) = Equiv.sym (soundness D)
    soundness (trans D D₁) = Equiv.trans (soundness D) (soundness D₁)
    soundness sub/id = identityʳ
    soundness sub/∙ = sym-assoc
    soundness (eta/Unit e) = T.!-unique ⟦ e ⟧
    soundness (beta/*₁ _ e₂) = project₁
    soundness (beta/*₂ e₁ _) = project₂
    soundness (eta/* _) = g-η
    soundness (beta/=> e e′) =
      begin
        ⟦ app (abs e) e′ ⟧
      ≈˘⟨ ∘-resp-≈ʳ (Equiv.trans ⁂∘⟨⟩ (⟨⟩-cong₂ identityʳ identityˡ)) ⟩
        eval′ ∘ (λg ⟦ e ⟧ ⁂ Category.id 𝒞) ∘ ⟨ Category.id 𝒞 , ⟦ e′ ⟧ ⟩
      ≈⟨ Equiv.trans sym-assoc (∘-resp-≈ˡ β′) ⟩
        ⟦ e [ ext Term.id e′ ] ⟧
      ∎
    soundness (eta/=> e) =
      begin
        ⟦ abs (app (e [ weaken ]) var) ⟧
      ≈˘⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ Equiv.refl identityˡ)) ⟩
        λg (eval′ ∘ ⟨ ⟦ e ⟧ ∘ π₁ , Category.id 𝒞 ∘ π₂ ⟩)
      ≈˘⟨ λ-cong (∘-resp-≈ʳ ⁂∘⟨⟩) ⟩
        λg (eval′ ∘ (⟦ e ⟧ ⁂ Category.id 𝒞) ∘ ⟨ π₁ , π₂ ⟩)
      ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ η)) ⟩
        λg (eval′ ∘ (⟦ e ⟧ ⁂ Category.id 𝒞) ∘ Category.id 𝒞)
      ≈⟨ λ-cong (∘-resp-≈ʳ identityʳ) ⟩
        λg (eval′ ∘ (⟦ e ⟧ ⁂ Category.id 𝒞))
      ≈⟨ η-exp′ ⟩
        ⟦ e ⟧
      ∎
    soundness (comm/func _ Γ′ γ f e) = assoc
    soundness (comm/unit _ Γ′ γ) = Equiv.sym (T.!-unique (T.! ∘ ⟦ γ ⟧S))
    soundness comm/pair = Product.∘-distribʳ-⟨⟩ product
    soundness comm/fst = assoc
    soundness comm/snd = assoc
    soundness (comm/abs {γ = γ} {e = e}) =
      begin
        λg ⟦ e ⟧ ∘ ⟦ γ ⟧S
      ≈⟨ exp.subst product product ⟩
        λg (⟦ e ⟧ ∘ (⟦ γ ⟧S ⁂ Category.id 𝒞))
      ≈˘⟨ λ-cong (∘-resp-≈ʳ (Equiv.trans (∘-resp-≈ʳ η) identityʳ)) ⟩
        λg (⟦ e ⟧ ∘ (⟦ γ ⟧S ⁂ Category.id 𝒞) ∘ ⟨ π₁ , π₂ ⟩)
      ≈⟨ λ-cong (∘-resp-≈ʳ (⁂∘⟨⟩)) ⟩
        λg (⟦ e ⟧ ∘ ⟨ ⟦ γ ⟧S ∘ π₁ , Category.id 𝒞 ∘ π₂ ⟩)
      ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ Equiv.refl identityˡ)) ⟩
        λg (⟦ e ⟧ ∘ ⟨ ⟦ γ ⟧S ∘ π₁ , π₂ ⟩ )
      ∎
    soundness comm/app = Equiv.trans assoc (∘-resp-≈ʳ ⟨⟩∘)
    soundness (var/ext γ _) = project₂
    soundness (cong/sub D D′) = ∘-resp-≈ (soundness D′) (soundness-sub D)
    soundness (cong/pair D D₁) = ⟨⟩-cong₂ (soundness D) (soundness D₁)
    soundness (cong/fst D) = ∘-resp-≈ʳ (soundness D)
    soundness (cong/snd D) = ∘-resp-≈ʳ (soundness D)
    soundness (cong/app D D₁) = ∘-resp-≈ʳ (⟨⟩-cong₂ (soundness D) (soundness D₁))
    soundness (cong/abs D) = λ-cong (soundness D)
    soundness (cong/func D) = ∘-resp-≈ Equiv.refl (soundness D)

    soundness-sub refl = Equiv.refl
    soundness-sub (sym D) = Equiv.sym (soundness-sub D)
    soundness-sub (trans D D₁) = Equiv.trans (soundness-sub D) (soundness-sub D₁)
    soundness-sub (!-unique {γ = γ}) = T.!-unique ⟦ γ ⟧S
    soundness-sub η-pair =
      begin
        ⟨ π₁ , π₂ ⟩
      ≈⟨ Product.η product ⟩
        Category.id 𝒞
      ∎
    soundness-sub ext∙ = ⟨⟩∘
    soundness-sub (cong/ext D D′) = ⟨⟩-cong₂ (soundness-sub D) (soundness D′)
    soundness-sub weaken/ext = project₁
    soundness-sub (cong/∙ D D₁) = ∘-resp-≈ (soundness-sub D) (soundness-sub D₁)
    soundness-sub id∙ˡ = identityˡ
    soundness-sub id∙ʳ = identityʳ
    soundness-sub assoc∙ = assoc
