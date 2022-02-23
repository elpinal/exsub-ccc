module Categories.Functor.CartesianClosed where

open import Categories.Category using (Category; _[_∘_]; _[_,_])
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Bundle using (CartesianClosedCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Cartesian using (IsCartesianF)
import Categories.Morphism as Morphism

open import Level

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record IsCartesianClosedF
  (C : CartesianClosedCategory o ℓ e)
  (D : CartesianClosedCategory o′ ℓ′ e′)
  (F : Functor (CartesianClosedCategory.U C) (CartesianClosedCategory.U D))
  : Set (levelOfTerm C ⊔ levelOfTerm D) where
  open Morphism (CartesianClosedCategory.U D) using (IsIso; Iso)
  open Functor F

  private
    CU = CartesianClosedCategory.U C
    DU = CartesianClosedCategory.U D
    CC₁ = CartesianClosedCategory.cartesianClosed C
    CC₂ = CartesianClosedCategory.cartesianClosed D
    C₁ = CartesianClosed.cartesian CC₁
    C₂ = CartesianClosed.cartesian CC₂
    C′ = record { U = CU ; cartesian = C₁ }
    D′ = record { U = DU ; cartesian = C₂ }
    _^C_ = CartesianClosed._^_ CC₁
    _^D_ = CartesianClosed._^_ CC₂

  field
    isCartesianF : IsCartesianF C′ D′ F

  conv : forall {A B : Category.Obj CU} -> DU [ F₀ (B ^C A) , F₀ B ^D F₀ A ]
  conv {A} {B} =
    CartesianClosed.λg CC₂
      (DU [ F₁ (CartesianClosed.eval′ CC₁) ∘ IsCartesianF.×-iso.to isCartesianF (B ^C A) A ])

  field
    F-preserve-^ : forall {A B : Category.Obj CU} -> IsIso (conv {A} {B})

  -- Note that F is called strict if `conv` ≈ id.
