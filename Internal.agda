open import Categories.Category
open import Categories.Category.CartesianClosed

{-
  The internal language of a given cartesian closed category.
-}
module Internal {o β e} (π : Category o β e)
  (cartesianClosed : CartesianClosed π) where

open import Relation.Binary using (Rel)
open import Data.Product using (Ξ£-syntax; _,_)
open import Level

open import Syntax
open import Theory

open import Categories.Category.Cartesian π
open import Categories.Category.BinaryProducts π
open import Categories.Object.Terminal π

open Category π
open CartesianClosed cartesianClosed
open Cartesian cartesian
open BinaryProducts products
module T = Terminal terminal

module _ where
  open PType Obj

  data F : Set (o β β) where
    Inherit : forall {A B : Obj} -> A β B -> F
    I : Type -> F
    J : Type -> F

  -- The same as β¦_β§T in Semantics.agda.
  β¦_β§Tβ² : Type -> Obj
  β¦ β A β β§Tβ² = A
  β¦ Unit β§Tβ² = T.β€
  β¦ A * Aβ β§Tβ² = β¦ A β§Tβ² Γ β¦ Aβ β§Tβ²
  β¦ A => Aβ β§Tβ² = β¦ A β§Tβ² β¨ β¦ Aβ β§Tβ²

  sorting : F -> Sorting
  sorting (Inherit {A} {B} f) = record { dom = β A β ; cod = β B β }
  sorting (I A) = record { dom = β β¦ A β§Tβ² β ; cod = A }
  sorting (J A) = record { dom = A ; cod = β β¦ A β§Tβ² β }

Sg : Signature o (o β β)
Sg = record { Gr = Obj ; Func = F ; sorting = sorting }

open Signature Sg
open Term Sg

open import Semantics π cartesianClosed Sg

open I (Ξ» x β x)

i : forall (A : Type) -> (β¦ β β¦ A β§Tβ² β β§T) β (β¦ A β§T)
j : forall (A : Type) -> (β¦ A β§T) β (β¦ β β¦ A β§Tβ² β β§T)

i β A β = Category.id π
i Unit = Category.id π
i (A * Aβ) = (i A) β (i Aβ)
i (A => Aβ) = Ξ»g (i Aβ β (evalβ² β (Category.id π β j A)))

j β A β = Category.id π
j Unit = Category.id π
j (A * Aβ) = j A β j Aβ
j (A => Aβ) = Ξ»g ((j Aβ β (evalβ² β (Category.id π β i A))))

S : Structure
S = record { β¦_β§G = Ξ» x β x ; β¦_β§F = Ξ» { (Inherit f) β f ; (I A) β i A ; (J A) β j A} }

open Structure S

data Ax (Ξ : Context) (A : Type) : Rel (Ξ β’ A) (o β β β e) where
  E : forall {eβ eβ} -> β¦ eβ β§ β β¦ eβ β§ -> Ax Ξ A eβ eβ

Th : Theory o (o β β) (o β β β e)
Th = record { Sg = Sg ; Ax = Ax }

M : Model π cartesianClosed Th
M = S , Ξ» { (E x) β x}
