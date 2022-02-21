module Syntax where

open import Data.List using (List; []; _∷_; _++_; lookup; length)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit renaming (⊤ to top)
open import Data.Empty renaming (⊥ to bot)

open import Level using (suc; _⊔_)

module PType {ℓ} (Gr : Set ℓ) where
  infixr 10 _*_
  infixr 9 _=>_

  data Type : Set ℓ where
    ⌊_⌋ : Gr -> Type
    Unit : Type
    _*_ : Type -> Type -> Type
    _=>_ : Type -> Type -> Type

  record Sorting : Set ℓ where
    field
      dom : Type
      cod : Type

  Context : Set ℓ
  Context = List Type

record Signature ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    Gr : Set ℓ₁
    Func : Set ℓ₂

  open PType Gr public

  field
    sorting : Func -> Sorting

  dom : Func -> Type
  dom f = Sorting.dom (sorting f)

  cod : Func -> Type
  cod f = Sorting.cod (sorting f)

module Term {ℓ₁ ℓ₂} (Sg : Signature ℓ₁ ℓ₂) where
  open Signature Sg

  infix 3 _⊨_
  infix 8 _∙_

  infix 3 _⊢_
  infixl 4 _[_]

  data _⊨_ : Context -> Context -> Set (ℓ₁ ⊔ ℓ₂)
  data _⊢_ : Context -> Type -> Set (ℓ₁ ⊔ ℓ₂)

  data _⊨_ where
    id : forall {Γ} -> Γ ⊨ Γ  -- identity morphism
    _∙_ : forall {Γ Γ′ Γ′′} -> Γ′ ⊨ Γ′′ -> Γ ⊨ Γ′ -> Γ ⊨ Γ′′ -- composition of morphisms
    weaken : forall {Γ A} -> A ∷ Γ ⊨ Γ -- the first projection
    ext : forall {Γ Γ′ A} -> Γ ⊨ Γ′ -> Γ ⊢ A -> Γ ⊨ A ∷ Γ′ -- the unique morphism into the product
    ! : forall {Γ} -> Γ ⊨ [] -- the unique morphism into the terminal object

  data _⊢_ where
    func : forall {Γ} (f : Func) -> Γ ⊢ dom f -> Γ ⊢ cod f

    var : forall {Γ A} -> A ∷ Γ ⊢ A

    unit : forall {Γ} -> Γ ⊢ Unit

    pair : forall {Γ A B} -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A * B
    fst : forall {Γ A B} -> Γ ⊢ A * B -> Γ ⊢ A
    snd : forall {Γ A B} -> Γ ⊢ A * B -> Γ ⊢ B

    abs : forall {Γ A B} -> A ∷ Γ ⊢ B -> Γ ⊢ A => B
    app : forall {Γ A B} -> Γ ⊢ A => B -> Γ ⊢ A -> Γ ⊢ B

    _[_] : forall {Γ Γ′ A} -> Γ′ ⊢ A -> Γ ⊨ Γ′ -> Γ ⊢ A
