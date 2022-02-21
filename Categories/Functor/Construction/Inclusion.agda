open import Theory

module Categories.Functor.Construction.Inclusion {ℓ₁ ℓ₂ ℓ₃} (Th : Theory ℓ₁ ℓ₂ ℓ₃) where

open import Syntax

open Theory.Theory Th
open Signature Sg
open Term Sg

open import Categories.Category.Construction.Renaming Sg as Renaming using (Ren; ren; _≐_)
open import Categories.Category.Construction.Classifying Th using (Cl; CC)

open import Categories.Functor
open import Categories.Category
open import Categories.Morphism Cl using (_≅_; Iso)
open import Categories.Category.CartesianClosed Cl
open import Categories.Category.Cartesian Cl
open import Categories.Category.BinaryProducts Cl

open import Data.List using (List; []; _∷_; _++_)
import Relation.Binary.Reasoning.Setoid as Reasoning
module TermReasoning {Γ A} = Reasoning (TermSetoid {Γ} {A})

inclusion : Functor Ren Cl
inclusion = record
      { F₀ = F₀
      ; F₁ = F₁
      ; identity = C.Equiv.refl
      ; homomorphism = λ {Γ₁} {Γ₂} {Γ₃} {f} {g} -> homomorphism f g
      ; F-resp-≈ = F-resp-≈
      }
  where
    module C = Category Cl
    open CartesianClosed CC
    open Cartesian cartesian
    open BinaryProducts products
    open import Categories.Morphism.Reasoning Cl

    id⁂id : forall {A B} -> C.id ⁂ C.id C.≈ C.id {A = A * B}
    id⁂id = trans (⟨⟩-cong₂ C.identityˡ C.identityˡ) η

    F₀ : Context -> Type
    F₀ [] = Unit
    F₀ (A ∷ Γ) = F₀ Γ * A

    F₀/*⇒++ : forall {Γ Δ} -> F₀ Γ * F₀ Δ C.⇒ F₀ (Δ ++ Γ)
    F₀/*⇒++ {Γ} {[]} = fst var
    F₀/*⇒++ {Γ} {A ∷ Δ} = (F₀/*⇒++ ⁂ C.id) C.∘ assocʳ

    F₀/++⇒* : forall {Γ Δ} -> F₀ (Δ ++ Γ) C.⇒ F₀ Γ * F₀ Δ
    F₀/++⇒* {Γ} {[]} = pair var unit
    F₀/++⇒* {Γ} {A ∷ Δ} = assocˡ C.∘ (F₀/++⇒* ⁂ C.id)

    F₀/*≅++ : forall {Γ Δ} -> F₀ Γ * F₀ Δ ≅ F₀ (Δ ++ Γ)
    F₀/*≅++ = record
      { from = F₀/*⇒++
      ; to = F₀/++⇒*
      ; iso = record { isoˡ = isoˡ ; isoʳ = isoʳ }
      }
      where
        isoˡ : forall {Γ Δ} -> F₀/++⇒* C.∘ F₀/*⇒++ C.≈ C.id {A = F₀ Γ * F₀ Δ}
        isoˡ {Γ} {[]} =
          begin
            pair var unit [ ext ! (fst var) ]
          ≈⟨ trans comm/pair (cong/pair (var/ext _ _) (comm/unit _ _ _)) ⟩
            pair (fst var) unit
          ≈⟨ cong/pair refl (eta/Unit _) ⟩
            pair (fst var) (snd var)
          ≈⟨ eta/* _ ⟩
            var
          ∎
          where open TermReasoning
        isoˡ {Γ} {A ∷ Δ} =
          begin
            (assocˡ C.∘ (F₀/++⇒* ⁂ var)) C.∘ ((F₀/*⇒++ ⁂ var) C.∘ assocʳ)
          ≈⟨ C.assoc ⟩
            assocˡ C.∘ (F₀/++⇒* ⁂ var) C.∘ (F₀/*⇒++ ⁂ var) C.∘ assocʳ
          ≈⟨ C.∘-resp-≈ʳ (pullˡ ⁂∘⁂) ⟩
            assocˡ C.∘ (F₀/++⇒* C.∘ F₀/*⇒++ ⁂ var C.∘ var) C.∘ assocʳ
          ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (⁂-cong₂ isoˡ C.identity²)) ⟩
            assocˡ C.∘ (var ⁂ var) C.∘ assocʳ
          ≈⟨ elim-center id⁂id ⟩
            assocˡ C.∘ assocʳ
          ≈⟨ assocˡ∘assocʳ ⟩
            var
          ∎
          where open TermReasoning

        isoʳ : forall {Γ Δ} -> F₀/*⇒++ C.∘ F₀/++⇒* {Γ = Γ} C.≈ C.id {A = F₀ (Δ ++ Γ)}
        isoʳ {Γ} {[]} = trans comm/fst (trans (cong/fst (var/ext _ _)) (beta/*₁ _ _))
        isoʳ {Γ} {A ∷ Δ} =
          begin
            ((F₀/*⇒++ ⁂ var) C.∘ assocʳ) C.∘ (assocˡ C.∘ (F₀/++⇒* ⁂ var))
          ≈⟨ cancelInner assocʳ∘assocˡ ⟩
            (F₀/*⇒++ ⁂ var) C.∘ (F₀/++⇒* ⁂ var)
          ≈⟨ ⁂∘⁂ ⟩
            F₀/*⇒++ C.∘ F₀/++⇒* ⁂ var C.∘ var
          ≈⟨ ⁂-cong₂ isoʳ C.identity² ⟩
            var ⁂ var
          ≈⟨ id⁂id ⟩
            var
          ∎
          where open TermReasoning

    F₁p : forall {Γ Δ} -> F₀ (Δ ++ Γ) ∷ [] ⊢ F₀ Γ
    F₁p = fst var C.∘ F₀/++⇒*

    F₁q : forall {Γ Δ} -> F₀ (Δ ++ Γ) ∷ [] ⊢ F₀ Δ
    F₁q = snd var C.∘ F₀/++⇒*

    F₁ : forall {Γ Δ : Context} -> ren Γ Δ -> F₀ Γ ∷ [] ⊢ F₀ Δ
    F₁ Renaming.id = C.id
    F₁ (r Renaming.∙ r₁) = F₁ r C.∘ F₁ r₁
    F₁ Renaming.! = unit
    F₁ Renaming.⟪ r , r₁ ⟫ = F₀/*⇒++ C.∘ pair (F₁ r) (F₁ r₁)
    F₁ Renaming.p = F₁p
    F₁ Renaming.q = F₁q

    homomorphism : forall {Γ₁ Γ₂ Γ₃} (f : ren Γ₁ Γ₂) (g : ren Γ₂ Γ₃)
      -> F₀ Γ₁ ∷ [] ⊢ F₁ g [ ext ! (F₁ f) ] ≡ F₁ g [ ext ! (F₁ f) ]
    homomorphism f g = refl

    F-resp-≈ : forall {Γ Δ} {f g : ren Γ Δ} -> f ≐ g -> F₀ Γ ∷ [] ⊢ F₁ f ≡ F₁ g
    F-resp-≈ _≐_.refl = refl
    F-resp-≈ (_≐_.sym x) = sym (F-resp-≈ x)
    F-resp-≈ (_≐_.trans x x₁) = trans (F-resp-≈ x) (F-resp-≈ x₁)
    F-resp-≈ _≐_.identityˡ = var/ext _ _
    F-resp-≈ _≐_.identityʳ = trans (cong/sub (trans (cong/ext !-unique refl) η-pair) refl) sub/id
    F-resp-≈ _≐_.assoc = C.assoc
    F-resp-≈ _≐_.!-unique = eta/Unit _
    F-resp-≈ _≐_.β₁/⟪⟫ = trans (cancelInner (Iso.isoˡ (_≅_.iso F₀/*≅++))) project₁
    F-resp-≈ _≐_.β₂/⟪⟫ = trans (cancelInner (Iso.isoˡ (_≅_.iso F₀/*≅++))) project₂
    F-resp-≈ _≐_.η/⟪⟫ = trans (C.∘-resp-≈ʳ (trans (⟨⟩-cong₂ C.assoc C.assoc) g-η)) (cancelˡ (Iso.isoʳ (_≅_.iso F₀/*≅++)))
    F-resp-≈ (_≐_.cong/∙ x x₁) = cong/sub (cong/ext refl (F-resp-≈ x₁)) (F-resp-≈ x)
    F-resp-≈ (_≐_.cong/⟪⟫ x x₁) = cong/sub (cong/ext refl (cong/pair (F-resp-≈ x) (F-resp-≈ x₁))) refl
