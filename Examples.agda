module Examples where

open import Data.List using ([]; [_])
open import Data.Fin using () renaming (zero to fzero)

open import Relation.Binary using (Rel)

open import Level using () renaming (zero to lzero)

open import Syntax
open import Theory

module NatBool where
  data Gr : Set where
    nat : Gr
    bool : Gr

  data Func : Set where
    zero plus true false not : Func

  open PType Gr

  sorting : Func -> Sorting
  sorting zero = record { dom = Unit ; cod = ⌊ nat ⌋ }
  sorting plus = record { dom = ⌊ nat ⌋ * ⌊ nat ⌋ ; cod = ⌊ nat ⌋ }
  sorting true = record { dom = Unit ; cod = ⌊ bool ⌋ }
  sorting false = record { dom = Unit ; cod = ⌊ bool ⌋ }
  sorting not = record { dom = ⌊ bool ⌋ ; cod = ⌊ bool ⌋ }

  Sg : Signature lzero lzero
  Sg = record { Gr = Gr ; Func = Func ; sorting = sorting }

  open Term Sg

  data Ax : forall Γ A -> Rel (Γ ⊢ A) lzero where
    not-true≡false : forall Γ -> Ax Γ ⌊ bool ⌋ (func not (func true unit)) (func false unit)
    not-false≡true : forall Γ -> Ax Γ ⌊ bool ⌋ (func not (func false unit)) (func true unit)
    plus-identityˡ : Ax [ ⌊ nat ⌋ ] ⌊ nat ⌋
      (func plus (pair (func zero unit) var))
      var

  Th : Theory lzero lzero lzero
  Th = record { Sg = Sg ; Ax = Ax }
