open import Syntax

module Categories.Category.Construction.Renaming {ℓ₁ ℓ₂} (Sg : Signature ℓ₁ ℓ₂) where

open import Relation.Binary using (Rel)
open import Data.List using (List; []; [_]; _∷_; length; _++_)
open import Level using (zero; _⊔_)

open import Categories.Category

open Signature Sg

data ren : Rel Context ℓ₁ where
  id : forall {Γ} -> ren Γ Γ
  _∙_ : forall {Γ₁ Γ₂ Γ₃} -> ren Γ₂ Γ₃ -> ren Γ₁ Γ₂ -> ren Γ₁ Γ₃
  ! : forall {Γ} -> ren Γ []
  ⟪_,_⟫ : forall {Γ Γ₁ Γ₂} -> ren Γ Γ₁ -> ren Γ Γ₂ -> ren Γ (Γ₂ ++ Γ₁)
  p : forall {Γ Γ′} -> ren (Γ′ ++ Γ) Γ
  q : forall {Γ Γ′} -> ren (Γ′ ++ Γ) Γ′

data _≐_ : forall {Γ Γ′} -> Rel (ren Γ Γ′) ℓ₁ where
  refl : forall {Γ Γ′} {f : ren Γ Γ′} -> f ≐ f
  sym : forall {Γ Γ′} {f g : ren Γ Γ′} -> f ≐ g -> g ≐ f
  trans : forall {Γ Γ′} {f g h : ren Γ Γ′} -> f ≐ g -> g ≐ h -> f ≐ h

  identityˡ : forall {Γ Γ′} {f : ren Γ Γ′} -> (id ∙ f) ≐ f
  identityʳ : forall {Γ Γ′} {f : ren Γ Γ′} -> (f ∙ id) ≐ f
  assoc : forall {Γ Γ′ Γ″ Γ‴} {h : ren Γ Γ′} {g : ren Γ′ Γ″} {f : ren Γ″ Γ‴}
    -> ((f ∙ g) ∙ h) ≐ (f ∙ (g ∙ h))

  !-unique : forall {Γ} {f : ren Γ []} -> ! ≐ f

  β₁/⟪⟫ : forall {Γ Γ₁ Γ₂} {f : ren Γ Γ₁} {g : ren Γ Γ₂} -> (p ∙ ⟪ f , g ⟫) ≐ f
  β₂/⟪⟫ : forall {Γ Γ₁ Γ₂} {f : ren Γ Γ₁} {g : ren Γ Γ₂} -> (q ∙ ⟪ f , g ⟫) ≐ g
  η/⟪⟫ : forall {Γ Γ₁ Γ₂} {f : ren Γ (Γ₂ ++ Γ₁)} -> ⟪ p {Γ = Γ₁} ∙ f , q {Γ′ = Γ₂} ∙ f ⟫ ≐ f

  cong/∙ : forall {Γ₁ Γ₂ Γ₃} {g i : ren Γ₁ Γ₂} {f h : ren Γ₂ Γ₃} -> f ≐ h -> g ≐ i -> (f ∙ g) ≐ (h ∙ i)
  cong/⟪⟫ : forall {Γ Γ₁ Γ₂} {f h : ren Γ Γ₁} {g i : ren Γ Γ₂} -> f ≐ h -> g ≐ i -> ⟪ f , g ⟫ ≐ ⟪ h , i ⟫

Ren : Category ℓ₁ ℓ₁ ℓ₁
Ren = record
        { Obj = Context
        ; _⇒_ = ren
        ; _≈_ = _≐_
        ; id = id
        ; _∘_ = _∙_
        ; assoc = assoc
        ; sym-assoc = sym assoc
        ; identityˡ = identityˡ
        ; identityʳ = identityʳ
        ; identity² = identityˡ
        ; equiv = record { refl = refl ; sym = sym ; trans = trans }
        ; ∘-resp-≈ = cong/∙
        }

open import Categories.Category.Cartesian Ren
open import Categories.Category.BinaryProducts Ren
open import Categories.Object.Product Ren
open import Categories.Object.Terminal Ren

private
  P : forall {Γ₁ Γ₂} -> Product Γ₁ Γ₂
  P {Γ₁} {Γ₂} = record
         { A×B = Γ₂ ++ Γ₁
         ; π₁ = p
         ; π₂ = q
         ; ⟨_,_⟩ = ⟪_,_⟫
         ; project₁ = β₁/⟪⟫
         ; project₂ = β₂/⟪⟫
         ; unique = λ x x₁ →
             begin
               ⟪ _ , _ ⟫
             ≈˘⟨ cong/⟪⟫ x x₁ ⟩
               ⟪ _ , _ ⟫
             ≈⟨ η/⟪⟫ ⟩
               _
             ∎
         }
    where open Category.HomReasoning Ren

C : Cartesian
C = record { terminal = T ; products = record { product = P } }
  where
    T : Terminal
    T = record { ⊤ = [] ; ⊤-is-terminal = record { ! = ! ; !-unique = λ f → !-unique {f = f} } }
