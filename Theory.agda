module Theory where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)

open import Relation.Binary using (Rel)

open import Level using (suc; _⊔_)

open import Syntax

record Theory ℓ₁ ℓ₂ ℓ₃ : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Sg : Signature ℓ₁ ℓ₂

  open Signature Sg
  open Term Sg

  field
    Ax : forall Γ A -> Rel (Γ ⊢ A) ℓ₃

  infix 3 _⊢_≡_

  -- Theorems
  data _⊢_≡_ : forall Γ {A} -> Γ ⊢ A -> Γ ⊢ A -> Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    ax : forall {Γ A e₁ e₂} -> Ax Γ A e₁ e₂ -> Γ ⊢ e₁ ≡ e₂

    refl : forall Γ {A} (e : Γ ⊢ A) -> Γ ⊢ e ≡ e
    sym : forall Γ {A} {e₁ : Γ ⊢ A} {e₂} -> Γ ⊢ e₁ ≡ e₂ -> Γ ⊢ e₂ ≡ e₁
    trans : forall Γ {A} {e₁ : Γ ⊢ A} {e₂ e₃} -> Γ ⊢ e₁ ≡ e₂ -> Γ ⊢ e₂ ≡ e₃ -> Γ ⊢ e₁ ≡ e₃

    sub/id : forall Γ {A} (e : Γ ⊢ A) -> Γ ⊢ e [ id ] ≡ e
    sub/∙ : forall Γ {A} {Γ′ Γ′′} (e : Γ′′ ⊢ A) (γ : Γ′ ⊨ Γ′′) δ -> Γ ⊢ e [ γ ∙ δ ] ≡ e [ γ ] [ δ ]

    eta/Unit : forall Γ (e : Γ ⊢ Unit) -> Γ ⊢ unit ≡ e

    beta/*₁ : forall Γ {A B} (e₁ : Γ ⊢ A) (e₂ : Γ ⊢ B) -> Γ ⊢ fst (pair e₁ e₂) ≡ e₁
    beta/*₂ : forall Γ {A B} (e₁ : Γ ⊢ A) (e₂ : Γ ⊢ B) -> Γ ⊢ snd (pair e₁ e₂) ≡ e₂
    eta/* : forall Γ {A B} (e : Γ ⊢ A * B) -> Γ ⊢ pair (fst e) (snd e) ≡ e

    beta/=> : forall Γ {A B} (e : A ∷ Γ ⊢ B) (e′ : Γ ⊢ A) -> Γ ⊢ app (abs e) e′ ≡ e [ ext id e′ ]
    eta/=> : forall Γ {A B} (e : Γ ⊢ A => B) -> Γ ⊢ abs (app (e [ weaken (_ ∷ []) ]) (var fzero (here A Γ))) ≡ e

    -- cong

    -- subst commutes with term formers
    comm/func : forall Γ Γ′ (γ : Γ ⊨ Γ′) f e
      -> Γ ⊢ func f e [ γ ] ≡ func f (e [ γ ])

    comm/unit : forall Γ Γ′ (γ : Γ ⊨ Γ′)
      -> Γ ⊢ unit [ γ ] ≡ unit

    comm/pair : forall Γ {A B} (e₁ : Γ ⊢ A) (e₂ : Γ ⊢ B) γ
      -> Γ ⊢ pair e₁ e₂ [ γ ] ≡ pair (e₁ [ γ ]) (e₂ [ γ ])
    comm/fst : forall Γ {A B} (e : Γ ⊢ A * B) γ
      -> Γ ⊢ fst e [ γ ] ≡ fst (e [ γ ])
    comm/snd : forall Γ {A B} (e : Γ ⊢ A * B) γ
      -> Γ ⊢ snd e [ γ ] ≡ snd (e [ γ ])

    comm/abs : forall Γ {A B} {Γ′} (e : A ∷ Γ′ ⊢ B) (γ : Γ ⊨ Γ′)
      -> Γ ⊢ (abs e) [ γ ] ≡ abs (e [ ext (γ ∙ weaken (A ∷ [])) (var fzero (here A Γ)) ])
    comm/app : forall Γ {A B} (e₁ : Γ ⊢ A => B) e₂ γ
      -> Γ ⊢ app e₁ e₂ [ γ ] ≡ app (e₁ [ γ ]) (e₂ [ γ ])

    var/weaken : forall Γ k A (p : Γ #[ k ]= A) Γ′
      -> Γ′ ++ Γ ⊢ var k p [ weaken Γ′ ] ≡ var (raise-by Γ′ k) (#[]=-raise-by Γ′ p)

    zero/ext : forall {Γ Γ′} (γ : Γ ⊨ Γ′) {A} (e : Γ ⊢ A)
      -> Γ ⊢ var fzero (here A Γ′) [ ext γ e ] ≡ e

    suc/ext : forall {Γ} Γ′ (γ : Γ ⊨ Γ′) {A B} (e : Γ ⊢ A) k (p : Γ′ #[ k ]= B)
      -> Γ ⊢ var (fsuc k) (there A p) [ ext γ e ] ≡ var k p [ γ ]
