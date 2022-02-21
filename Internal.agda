open import Categories.Category
open import Categories.Category.CartesianClosed

{-
  The internal language of a given cartesian closed category.
-}
module Internal {o ℓ e} (𝒞 : Category o ℓ e)
  (cartesianClosed : CartesianClosed 𝒞) where

open import Relation.Binary using (Rel)
open import Data.Product using (Σ-syntax; _,_)
open import Level

open import Syntax
open import Theory

open import Categories.Category.Cartesian 𝒞
open import Categories.Category.BinaryProducts 𝒞
open import Categories.Object.Terminal 𝒞

open Category 𝒞
open CartesianClosed cartesianClosed
open Cartesian cartesian
open BinaryProducts products
module T = Terminal terminal

module _ where
  open PType Obj

  data F : Set (o ⊔ ℓ) where
    Inherit : forall {A B : Obj} -> A ⇒ B -> F
    I : Type -> F
    J : Type -> F

  -- The same as ⟦_⟧T in Semantics.agda.
  ⟦_⟧T′ : Type -> Obj
  ⟦ ⌊ A ⌋ ⟧T′ = A
  ⟦ Unit ⟧T′ = T.⊤
  ⟦ A * A₁ ⟧T′ = ⟦ A ⟧T′ × ⟦ A₁ ⟧T′
  ⟦ A => A₁ ⟧T′ = ⟦ A ⟧T′ ⇨ ⟦ A₁ ⟧T′

  sorting : F -> Sorting
  sorting (Inherit {A} {B} f) = record { dom = ⌊ A ⌋ ; cod = ⌊ B ⌋ }
  sorting (I A) = record { dom = ⌊ ⟦ A ⟧T′ ⌋ ; cod = A }
  sorting (J A) = record { dom = A ; cod = ⌊ ⟦ A ⟧T′ ⌋ }

Sg : Signature o (o ⊔ ℓ)
Sg = record { Gr = Obj ; Func = F ; sorting = sorting }

open Signature Sg
open Term Sg

open import Semantics 𝒞 cartesianClosed Sg

open I (λ x → x)

i : forall (A : Type) -> (⟦ ⌊ ⟦ A ⟧T′ ⌋ ⟧T) ⇒ (⟦ A ⟧T)
j : forall (A : Type) -> (⟦ A ⟧T) ⇒ (⟦ ⌊ ⟦ A ⟧T′ ⌋ ⟧T)

i ⌊ A ⌋ = Category.id 𝒞
i Unit = Category.id 𝒞
i (A * A₁) = (i A) ⁂ (i A₁)
i (A => A₁) = λg (i A₁ ∘ (eval′ ∘ (Category.id 𝒞 ⁂ j A)))

j ⌊ A ⌋ = Category.id 𝒞
j Unit = Category.id 𝒞
j (A * A₁) = j A ⁂ j A₁
j (A => A₁) = λg ((j A₁ ∘ (eval′ ∘ (Category.id 𝒞 ⁂ i A))))

S : Structure
S = record { ⟦_⟧G = λ x → x ; ⟦_⟧F = λ { (Inherit f) → f ; (I A) → i A ; (J A) → j A} }

open Structure S

data Ax (Γ : Context) (A : Type) : Rel (Γ ⊢ A) (o ⊔ ℓ ⊔ e) where
  E : forall {e₁ e₂} -> ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧ -> Ax Γ A e₁ e₂

Th : Theory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Th = record { Sg = Sg ; Ax = Ax }

M : Model 𝒞 cartesianClosed Th
M = S , λ { (E x) → x}
