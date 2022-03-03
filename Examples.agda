module Examples where

open import Data.List using ([]; _∷_)
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
    not-true≡false : Ax [] ⌊ bool ⌋ (func not (func true unit)) (func false unit)
    not-false≡true : Ax [] ⌊ bool ⌋ (func not (func false unit)) (func true unit)
    plus-identityˡ : Ax (⌊ nat ⌋ ∷ []) ⌊ nat ⌋
      (func plus (pair (func zero unit) var))
      var

  Th : Theory lzero lzero lzero
  Th = record { Sg = Sg ; Ax = Ax }

  open Theory.Theory Th

  import Relation.Binary.Reasoning.Setoid as S

  thm1 : forall {Γ} -> Γ ⊢ func not (func true unit) ≡ func false unit
  thm1 =
    begin
      func not (func true unit)
    ≈˘⟨ cong/func (cong/func (comm/unit _ _ _)) ⟩
      func not (func true (unit [ ! ]))
    ≈˘⟨ cong/func (comm/func _ _ _ _ _) ⟩
      func not (func true unit [ ! ])
    ≈˘⟨ comm/func _ _ _ _ _ ⟩
      func not (func true unit) [ ! ]
    ≈⟨ cong/sub refl (ax not-true≡false) ⟩
      func false unit [ ! ]
    ≈⟨ comm/func _ _ _ _ _ ⟩
      func false (unit [ ! ])
    ≈⟨ cong/func (comm/unit _ _ _) ⟩
      func false unit
    ∎
    where open S TermSetoid
