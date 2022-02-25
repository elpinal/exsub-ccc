open import Categories.Category using (Category)
import Categories.Category.CartesianClosed

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)

open import Syntax

open import Level using (_⊔_; suc)

module Semantics {o ℓ e}
  (𝒞 : Category o ℓ e)
  (CC : Categories.Category.CartesianClosed.CartesianClosed 𝒞)
  {ℓ₁ ℓ₂}
  (Sg : Signature ℓ₁ ℓ₂)
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
  module T = Terminal terminal -- TODO: make this private.

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
    ⟦ var ⟧ = π₂
    ⟦ unit ⟧ = T.!
    ⟦ pair e e₁ ⟧ = ⟨ ⟦ e ⟧ , ⟦ e₁ ⟧ ⟩
    ⟦ fst e ⟧ = π₁ ∘ ⟦ e ⟧
    ⟦ snd e ⟧ = π₂ ∘ ⟦ e ⟧
    ⟦ abs e ⟧ = λg ⟦ e ⟧
    ⟦ app e e₁ ⟧ = eval′ ∘ ⟨ ⟦ e ⟧ , ⟦ e₁ ⟧ ⟩
    ⟦ e [ γ ] ⟧ = ⟦ e ⟧ ∘ ⟦ γ ⟧S

    ⟦ id ⟧S = Category.id 𝒞
    ⟦ γ ∙ γ₁ ⟧S = ⟦ γ ⟧S ∘ ⟦ γ₁ ⟧S
    ⟦ weaken ⟧S = π₁
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
