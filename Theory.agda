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
  infix 3 _⊨_≡_

  data _⊢_≡_ : forall Γ {A} -> Γ ⊢ A -> Γ ⊢ A -> Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  data _⊨_≡_ : forall Γ {Γ′} -> Γ ⊨ Γ′ -> Γ ⊨ Γ′ -> Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

  -- Theorems
  data _⊢_≡_ where
    ax : forall {Γ A e₁ e₂} -> Ax Γ A e₁ e₂ -> Γ ⊢ e₁ ≡ e₂

    refl : forall {Γ} {A} {e : Γ ⊢ A} -> Γ ⊢ e ≡ e
    sym : forall {Γ} {A} {e₁ : Γ ⊢ A} {e₂} -> Γ ⊢ e₁ ≡ e₂ -> Γ ⊢ e₂ ≡ e₁
    trans : forall {Γ} {A} {e₁ : Γ ⊢ A} {e₂ e₃} -> Γ ⊢ e₁ ≡ e₂ -> Γ ⊢ e₂ ≡ e₃ -> Γ ⊢ e₁ ≡ e₃

    sub/id : forall {Γ} {A} {e : Γ ⊢ A} -> Γ ⊢ e [ id ] ≡ e
    sub/∙ : forall {Γ} {A} {Γ′ Γ′′} {e : Γ′′ ⊢ A} {γ : Γ′ ⊨ Γ′′} {δ}
      -> Γ ⊢ e [ γ ∙ δ ] ≡ e [ γ ] [ δ ]

    eta/Unit : forall {Γ} (e : Γ ⊢ Unit) -> Γ ⊢ unit ≡ e

    beta/*₁ : forall {Γ} {A B} (e₁ : Γ ⊢ A) (e₂ : Γ ⊢ B) -> Γ ⊢ fst (pair e₁ e₂) ≡ e₁
    beta/*₂ : forall {Γ} {A B} (e₁ : Γ ⊢ A) (e₂ : Γ ⊢ B) -> Γ ⊢ snd (pair e₁ e₂) ≡ e₂
    eta/* : forall {Γ} {A B} (e : Γ ⊢ A * B) -> Γ ⊢ pair (fst e) (snd e) ≡ e

    beta/=> : forall {Γ} {A B} (e : A ∷ Γ ⊢ B) (e′ : Γ ⊢ A) -> Γ ⊢ app (abs e) e′ ≡ e [ ext id e′ ]
    eta/=> : forall {Γ} {A B} (e : Γ ⊢ A => B) -> Γ ⊢ abs (app (e [ weaken ]) var) ≡ e

    -- cong
    cong/sub : forall {Γ Γ′} {γ γ′ : Γ ⊨ Γ′} {A} {e e′ : Γ′ ⊢ A}
      -> Γ ⊨ γ ≡ γ′
      -> Γ′ ⊢ e ≡ e′
      -> Γ ⊢ e [ γ ] ≡ e′ [ γ′ ]
    cong/pair : forall {Γ} {A B} {e₁ e₁′ : Γ ⊢ A} {e₂ e₂′ : Γ ⊢ B}
      -> Γ ⊢ e₁ ≡ e₁′
      -> Γ ⊢ e₂ ≡ e₂′
      -> Γ ⊢ pair e₁ e₂ ≡ pair e₁′ e₂′
    cong/fst : forall {Γ} {A B} {e e′ : Γ ⊢ A * B}
      -> Γ ⊢ e ≡ e′
      -> Γ ⊢ fst e ≡ fst e′
    cong/snd : forall {Γ} {A B} {e e′ : Γ ⊢ A * B}
      -> Γ ⊢ e ≡ e′
      -> Γ ⊢ snd e ≡ snd e′
    cong/abs : forall {Γ} {A B} {e e′ : A ∷ Γ ⊢ B}
      -> A ∷ Γ ⊢ e ≡ e′
      -> Γ ⊢ abs e ≡ abs e′
    cong/app : forall {Γ} {A B} {e₁ e₁′ : Γ ⊢ A => B} {e₂ e₂′ : Γ ⊢ A}
      -> Γ ⊢ e₁ ≡ e₁′
      -> Γ ⊢ e₂ ≡ e₂′
      -> Γ ⊢ app e₁ e₂ ≡ app e₁′ e₂′

    -- subst commutes with term formers
    comm/func : forall Γ Γ′ (γ : Γ ⊨ Γ′) f e
      -> Γ ⊢ func f e [ γ ] ≡ func f (e [ γ ])

    comm/unit : forall Γ Γ′ (γ : Γ ⊨ Γ′)
      -> Γ ⊢ unit [ γ ] ≡ unit

    comm/pair : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A B} {e₁ : Γ′ ⊢ A} {e₂ : Γ′ ⊢ B}
      -> Γ ⊢ pair e₁ e₂ [ γ ] ≡ pair (e₁ [ γ ]) (e₂ [ γ ])
    comm/fst : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A B} {e : Γ′ ⊢ A * B}
      -> Γ ⊢ fst e [ γ ] ≡ fst (e [ γ ])
    comm/snd : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A B} {e : Γ′ ⊢ A * B}
      -> Γ ⊢ snd e [ γ ] ≡ snd (e [ γ ])

    comm/abs : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A B} {e : A ∷ Γ′ ⊢ B}
      -> Γ ⊢ (abs e) [ γ ] ≡ abs (e [ ext (γ ∙ weaken) var ])
    comm/app : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A B} {e₁ : Γ′ ⊢ A => B} {e₂}
      -> Γ ⊢ app e₁ e₂ [ γ ] ≡ app (e₁ [ γ ]) (e₂ [ γ ])

    var/ext : forall {Γ Γ′} (γ : Γ ⊨ Γ′) {A} (e : Γ ⊢ A)
      -> Γ ⊢ var [ ext γ e ] ≡ e

  data _⊨_≡_ where
    refl : forall {Γ Γ′} {γ : Γ ⊨ Γ′} -> Γ ⊨ γ ≡ γ
    sym : forall {Γ Γ′} {γ γ′ : Γ ⊨ Γ′} -> Γ ⊨ γ ≡ γ′ -> Γ ⊨ γ′ ≡ γ
    trans : forall {Γ Γ′} {γ₁ γ₂ γ₃ : Γ ⊨ Γ′}
      -> Γ ⊨ γ₁ ≡ γ₂
      -> Γ ⊨ γ₂ ≡ γ₃
      -> Γ ⊨ γ₁ ≡ γ₃

    id∙ˡ : forall {Γ Γ′} {γ : Γ ⊨ Γ′} -> Γ ⊨ id ∙ γ ≡ γ
    id∙ʳ : forall {Γ Γ′} {γ : Γ ⊨ Γ′} -> Γ ⊨ γ ∙ id ≡ γ

    -- associativity

    !-unique : forall {Γ} {γ : Γ ⊨ []} -> Γ ⊨ ! ≡ γ
    η-pair : forall {Γ : Context} {A : Type}
      -> A ∷ Γ ⊨ ext weaken var ≡ id
    ext∙ : forall {Γ Γ′ Γ′′} {γ : Γ′ ⊨ Γ′′} {γ′ : Γ ⊨ Γ′} {A} {e : Γ′ ⊢ A}
      -> Γ ⊨ ext γ e ∙ γ′ ≡ ext (γ ∙ γ′) (e [ γ′ ])

    weaken/ext : forall {Γ Γ′} {γ : Γ ⊨ Γ′} {A} {e : Γ ⊢ A}
      -> Γ ⊨ weaken ∙ ext γ e ≡ γ

    cong/ext : forall {Γ Γ′} {γ γ′ : Γ ⊨ Γ′} {A} {e e′ : Γ ⊢ A}
      -> Γ ⊨ γ ≡ γ′
      -> Γ ⊢ e ≡ e′
      -> Γ ⊨ ext γ e ≡ ext γ′ e′
    cong/∙ : forall {Γ Γ′ Γ′′} {γ γ′ : Γ′ ⊨ Γ′′} {δ δ′ : Γ ⊨ Γ′}
      -> Γ′ ⊨ γ ≡ γ′
      -> Γ ⊨ δ ≡ δ′
      -> Γ ⊨ γ ∙ δ ≡ γ′ ∙ δ′

  open import Relation.Binary.Bundles

  TermSetoid : forall {Γ : Context} {A : Type} -> Setoid (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  TermSetoid {Γ} {A} = record
             { Carrier = Γ ⊢ A
             ; _≈_ = λ e₁ e₂ → Γ ⊢ e₁ ≡ e₂
             ;isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
             }

open import Categories.Category
open import Categories.Category.CartesianClosed

module _ {o ℓ e} (𝒞 : Category o ℓ e) (CC : CartesianClosed 𝒞) {ℓ₁ ℓ₂ ℓ₃} (Th : Theory ℓ₁ ℓ₂ ℓ₃) where
  open Category 𝒞
  open import Data.Product using (Σ-syntax)
  open Theory Th
  open import Semantics 𝒞 CC Sg

  Model : Set (o ⊔ ℓ ⊔ e ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  Model = Σ[ M ∈ Structure ] forall {Γ A e₁ e₂} -> Ax Γ A e₁ e₂ -> ⟦ e₁ ⟧ M ≈ ⟦ e₂ ⟧ M
