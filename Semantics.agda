open import Categories.Category using (Category)
import Categories.Category.CartesianClosed

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)

open import Syntax
open import Theory

open import Level using (_⊔_; suc)

module Semantics {o ℓ e}
  (𝒞 : Category o ℓ e)
  (CC : Categories.Category.CartesianClosed.CartesianClosed 𝒞)
  {ℓ₁ ℓ₂ ℓ₃}
  (Th : Theory ℓ₁ ℓ₂ ℓ₃)
  where
  open Categories.Category.CartesianClosed 𝒞
  open import Categories.Category.Cartesian 𝒞
  open import Categories.Category.BinaryProducts 𝒞
  open import Categories.Object.Terminal 𝒞
  open import Categories.Object.Product 𝒞

  open Category 𝒞

  open CartesianClosed CC
  open Cartesian cartesian
  open BinaryProducts products
  module T = Terminal terminal

  open Theory.Theory Th
  open Signature Sg
  open Term Sg

  module I (⟦_⟧G : Gr -> Obj) where
    ⟦_⟧T : Type -> Obj
    ⟦ PType.⌊ g ⌋ ⟧T = ⟦ g ⟧G
    ⟦ PType.Unit ⟧T = T.⊤
    ⟦ A PType.* A₁ ⟧T = ⟦ A ⟧T × ⟦ A₁ ⟧T
    ⟦ A PType.=> A₁ ⟧T = ⟦ A ⟧T ⇨ ⟦ A₁ ⟧T

  record Structure : Set (o ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ⟦_⟧G : Gr -> Obj

    open I ⟦_⟧G public

    field
      ⟦_⟧F : (f : Func) -> ⟦ dom f ⟧T ⇒ ⟦ cod f ⟧T

    ⟦_⟧C : Context -> Obj
    ⟦ [] ⟧C = T.⊤
    ⟦ A ∷ Γ ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

    ⟦_⟧ : forall {Γ A} -> Γ ⊢ A -> ⟦ Γ ⟧C ⇒ ⟦ A ⟧T
    ⟦_⟧S : forall {Γ Γ′} -> Γ ⊨ Γ′ -> ⟦ Γ ⟧C ⇒ ⟦ Γ′ ⟧C

    ⟦ func f e ⟧ = ⟦ f ⟧F ∘ ⟦ e ⟧
    ⟦ var _ (here _ Γ) ⟧ = π₂
    ⟦ var _ (there _ p) ⟧ = ⟦ var _ p ⟧ ∘ π₁
    ⟦ unit ⟧ = T.!
    ⟦ pair e e₁ ⟧ = ⟨ ⟦ e ⟧ , ⟦ e₁ ⟧ ⟩
    ⟦ fst e ⟧ = π₁ ∘ ⟦ e ⟧
    ⟦ snd e ⟧ = π₂ ∘ ⟦ e ⟧
    ⟦ abs e ⟧ = λg ⟦ e ⟧
    ⟦ app e e₁ ⟧ = eval′ ∘ ⟨ ⟦ e ⟧ , ⟦ e₁ ⟧ ⟩
    ⟦ e [ γ ] ⟧ = ⟦ e ⟧ ∘ ⟦ γ ⟧S

    ⟦ id ⟧S = Category.id 𝒞
    ⟦ γ ∙ γ₁ ⟧S = ⟦ γ ⟧S ∘ ⟦ γ₁ ⟧S
    ⟦ weaken [] ⟧S = Category.id 𝒞
    ⟦ weaken (_ ∷ Γ′) ⟧S = ⟦ weaken Γ′ ⟧S ∘ π₁
    ⟦ ext γ e ⟧S = ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩
    ⟦ ! ⟧S = T.!

  ⟦_⟧G_ : Gr -> (M : Structure) -> Obj
  ⟦_⟧G_ g M = Structure.⟦_⟧G M g

  ⟦_⟧T_ : Type -> (M : Structure) -> Obj
  ⟦_⟧T_ A M = Structure.⟦_⟧T M A

  ⟦_⟧F_ : (f : Func) -> (M : Structure) -> Structure.⟦_⟧T M (dom f) ⇒ Structure.⟦_⟧T M (cod f)
  ⟦_⟧F_ f M = Structure.⟦_⟧F M f

  ⟦_⟧_ : forall {Γ A} -> Γ ⊢ A -> (M : Structure) -> Structure.⟦_⟧C M Γ ⇒ Structure.⟦_⟧T M A
  ⟦_⟧_ e M = Structure.⟦_⟧ M e

  Model : Set (o ⊔ ℓ ⊔ e ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  Model = Σ[ M ∈ Structure ] forall {Γ A e₁ e₂} -> Ax Γ A e₁ e₂ -> ⟦ e₁ ⟧ M ≈ ⟦ e₂ ⟧ M

  module _ (M : Model) where
    open Structure (proj₁ M)
    open HomReasoning

    soundness : forall {Γ A} {e₁ e₂ : Γ ⊢ A}
      -> Γ ⊢ e₁ ≡ e₂
      -> ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
    soundness (ax x) = proj₂ M x
    soundness (refl _ _) = Equiv.refl
    soundness (sym _ D) = Equiv.sym (soundness D)
    soundness (trans _ D D₁) = Equiv.trans (soundness D) (soundness D₁)
    soundness (sub/id _ _) = identityʳ
    soundness (sub/∙ _ e γ δ) = sym-assoc
    soundness (eta/Unit _ e) = T.!-unique ⟦ e ⟧
    soundness (beta/*₁ _ _ e₂) = project₁
    soundness (beta/*₂ _ e₁ _) = project₂
    soundness (eta/* _ _) = g-η
    soundness (beta/=> _ e e′) =
      begin
        ⟦ app (abs e) e′ ⟧
      ≈˘⟨ ∘-resp-≈ʳ (Equiv.trans ⁂∘⟨⟩ (⟨⟩-cong₂ identityʳ identityˡ)) ⟩
        eval′ ∘ (λg ⟦ e ⟧ ⁂ Category.id 𝒞) ∘ ⟨ Category.id 𝒞 , ⟦ e′ ⟧ ⟩
      ≈⟨ Equiv.trans sym-assoc (∘-resp-≈ˡ β′) ⟩
        ⟦ e [ ext Term.id e′ ] ⟧
      ∎
    soundness (eta/=> _ _) =
      Equiv.trans (λ-cong (∘-resp-≈ʳ (Equiv.trans (Equiv.trans (⟨⟩-cong₂ (∘-resp-≈ʳ identityˡ) (Equiv.sym identityˡ)) (Equiv.sym ⁂∘⟨⟩)) (Equiv.trans (∘-resp-≈ʳ η) identityʳ)))) η-exp′
    soundness (comm/func _ Γ′ γ f e) = assoc
    soundness (comm/unit _ Γ′ γ) = Equiv.sym (T.!-unique (T.! ∘ ⟦ γ ⟧S))
    soundness (comm/pair _ e₁ e₂ γ) = Product.∘-distribʳ-⟨⟩ product
    soundness (comm/fst _ e γ) = assoc
    soundness (comm/snd _ e γ) = assoc
    soundness (comm/abs _ e γ) =
      begin
        λg ⟦ e ⟧ ∘ ⟦ γ ⟧S
      ≈⟨ exp.subst product product ⟩
        λg (⟦ e ⟧ ∘ (⟦ γ ⟧S ⁂ Category.id 𝒞))
      ≈˘⟨ λ-cong (∘-resp-≈ʳ (Equiv.trans (∘-resp-≈ʳ η) identityʳ)) ⟩
        λg (⟦ e ⟧ ∘ (⟦ γ ⟧S ⁂ Category.id 𝒞) ∘ ⟨ π₁ , π₂ ⟩)
      ≈⟨ λ-cong (∘-resp-≈ʳ (⁂∘⟨⟩)) ⟩
        λg (⟦ e ⟧ ∘ ⟨ ⟦ γ ⟧S ∘ π₁ , Category.id 𝒞 ∘ π₂ ⟩)
      ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ (∘-resp-≈ʳ (Equiv.sym identityˡ)) identityˡ)) ⟩
        λg (⟦ e ⟧ ∘ ⟨ ⟦ γ ⟧S ∘ Category.id 𝒞 ∘ π₁ , π₂ ⟩ )
      ∎
    soundness (comm/app _ e₁ e₂ γ) = Equiv.trans assoc (∘-resp-≈ʳ ⟨⟩∘)
    soundness (Theory.var/weaken Γ k _ p []) = identityʳ
    soundness (Theory.var/weaken Γ k _ p (_ ∷ Γ′)) =
      Equiv.trans
        sym-assoc
        (∘-resp-≈ˡ (soundness (var/weaken Γ k _ p Γ′)))
    soundness (zero/ext γ _) = project₂
    soundness (suc/ext Γ′ γ e k p) = Equiv.trans assoc (∘-resp-≈ʳ project₁)
