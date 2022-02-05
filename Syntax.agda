module Syntax where

open import Data.Fin using (Fin; zero) renaming (suc to fsuc)
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

  data _#[_]=_ : (Γ : Context) -> Fin (length Γ) -> Type -> Set ℓ where
    here  : forall A Γ     -> (A ∷ Γ) #[ zero ]= A
    there : forall {A} B {Γ} {i} -> Γ #[ i ]= A -> (B ∷ Γ) #[ fsuc i ]= A

  lookup-#[]= : forall Γ k -> Γ #[ k ]= lookup Γ k
  lookup-#[]= (A ∷ Γ) zero = here A Γ
  lookup-#[]= (B ∷ Γ) (fsuc k) = there B (lookup-#[]= Γ k)

  raise-by : forall {Γ : Context} Γ′
    -> Fin (length Γ)
    -> Fin (length (Γ′ ++ Γ))
  raise-by [] k = k
  raise-by (_ ∷ Γ′) k = fsuc (raise-by Γ′ k)

  #[]=-raise-by : forall {Γ} (Γ′ : Context) {k : Fin (length Γ)} {A}
    -> Γ #[ k ]= A
    -> (Γ′ ++ Γ) #[ raise-by Γ′ k ]= A
  #[]=-raise-by [] p = p
  #[]=-raise-by (B ∷ Γ′) p = there B (#[]=-raise-by Γ′ p)

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
  data _⊢_ (Γ : Context) : Type -> Set (ℓ₁ ⊔ ℓ₂)

  data _⊨_ where
    id : forall {Γ} -> Γ ⊨ Γ  -- identity morphism
    _∙_ : forall {Γ Γ′ Γ′′} -> Γ′ ⊨ Γ′′ -> Γ ⊨ Γ′ -> Γ ⊨ Γ′′ -- composition of morphisms
    weaken : forall {Γ} Γ′ -> Γ′ ++ Γ ⊨ Γ
    ext : forall {Γ Γ′ A} -> Γ ⊨ Γ′ -> Γ ⊢ A -> Γ ⊨ A ∷ Γ′
    ! : forall {Γ} -> Γ ⊨ [] -- the unique morphism into the terminal object

  data _⊢_ Γ where
    func : forall (f : Func) -> Γ ⊢ dom f -> Γ ⊢ cod f

    var : forall {A} (k : Fin (length Γ)) -> Γ #[ k ]= A -> Γ ⊢ A

    unit : Γ ⊢ Unit

    pair : forall {A B} -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A * B
    fst : forall {A B} -> Γ ⊢ A * B -> Γ ⊢ A
    snd : forall {A B} -> Γ ⊢ A * B -> Γ ⊢ B

    abs : forall {A B} -> A ∷ Γ ⊢ B -> Γ ⊢ A => B
    app : forall {A B} -> Γ ⊢ A => B -> Γ ⊢ A -> Γ ⊢ B

    _[_] : forall {A Γ′} -> Γ′ ⊢ A -> Γ ⊨ Γ′ -> Γ ⊢ A
