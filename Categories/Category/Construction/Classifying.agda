open import Theory

module Categories.Category.Construction.Classifying {ℓ₁ ℓ₂ ℓ₃} (Th : Theory ℓ₁ ℓ₂ ℓ₃) where

open import Relation.Binary using (Rel)
open import Data.List using ([]; _∷_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Level using (_⊔_)

open import Categories.Category

open import Syntax

open Theory.Theory Th
open Signature Sg
open Term Sg

private
  arr : Rel Type (ℓ₁ ⊔ ℓ₂)
  arr A B = A ∷ [] ⊢ B

  identityʳ : forall {A B} {e : A ∷ [] ⊢ B}
    -> A ∷ [] ⊢ e [ ext ! var ] ≡ e
  identityʳ {A} {e = e} = trans (cong/sub (trans (cong/ext !-unique refl) η-pair) refl) sub/id

  assoc : {A B C D : Type} {f : arr A B} {g : arr B C} {h : arr C D}
    -> A ∷ [] ⊢ h [ ext ! g ] [ ext ! f ] ≡ h [ ext ! (g [ ext ! f ]) ]
  assoc {f = f} {g = g} {h = h} = trans (sym sub/∙)
    (cong/sub (trans ext∙ (cong/ext (sym !-unique) refl)) refl)

Cl : Category ℓ₁ (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
Cl = record
       { Obj = Type
       ; _⇒_ = arr
       ; _≈_ = λ e₁ e₂ → _ ∷ [] ⊢ e₁ ≡ e₂
       ; id = var
       ; _∘_ = λ e₁ e₂ → e₁ [ ext ! e₂ ]
       ; assoc = assoc
       ; sym-assoc = sym assoc
       ; identityˡ = λ {A} {B} {f} -> var/ext ! f
       ; identityʳ = identityʳ
       ; identity² = var/ext ! var
       ; equiv = record { refl = refl ; sym = sym ; trans = trans }
       ; ∘-resp-≈ = λ x x₁ → cong/sub (cong/ext refl x₁) x
       }

open import Categories.Category.BinaryProducts Cl

module M where
  open import Categories.Category.CartesianClosed.Canonical Cl

  CC : CartesianClosed
  CC = record
         { ⊤ = Unit
         ; _×_ = _*_
         ; ! = unit
         ; π₁ = fst var
         ; π₂ = snd var
         ; ⟨_,_⟩ = pair
         ; !-unique = eta/Unit
         ; π₁-comp = trans comm/fst (trans (cong/fst (var/ext ! (pair _ _))) (beta/*₁ _ _))
         ; π₂-comp = trans comm/snd (trans (cong/snd (var/ext ! (pair _ _))) (beta/*₂ _ _))
         ; ⟨,⟩-unique = ⟨,⟩-unique
         ; _^_ = λ A B → B => A
         ; eval = app (fst var) (snd var)
         ; curry = λ e → abs (e [ ext ! (pair (var [ weaken ]) var) ])
         ; eval-comp = eval-comp
         ; curry-resp-≈ = λ x → cong/abs (cong/sub refl x)
         ; curry-unique = λ x → curry-unique x
         }
    where
      ⟨,⟩-unique : forall {A B C} {h : C ∷ [] ⊢ A * B} {i : C ∷ [] ⊢ A} {j : C ∷ [] ⊢ B}
        -> C ∷ [] ⊢ fst var [ ext ! h ] ≡ i
        -> C ∷ [] ⊢ snd var [ ext ! h ] ≡ j
        -> C ∷ [] ⊢ pair i j ≡ h
      ⟨,⟩-unique x y = trans
        (cong/pair
          (sym (trans (cong/fst (sym (var/ext ! _))) (trans (sym comm/fst) x)))
          (sym (trans (cong/snd (sym (var/ext ! _))) (trans (sym comm/snd) y)))
        )
        (eta/* _)

      open import Categories.Object.Product.Morphisms Cl using ([_⇒_]_×_)
      open import Categories.Object.Product Cl using (Product)

      product : forall {A B} -> Product A B
      product {A} {B} = record
                          { A×B = A * B
                          ; π₁ = fst var
                          ; π₂ = snd var
                          ; ⟨_,_⟩ = pair
                          ; project₁ = trans comm/fst (trans (cong/fst (var/ext ! (pair _ _))) (beta/*₁ _ _))
                          ; project₂ = trans comm/snd (trans (cong/snd (var/ext ! (pair _ _))) (beta/*₂ _ _))
                          ; unique = ⟨,⟩-unique
                          }

      eval-comp : forall {B A C} {f : arr (C * A) B}
        -> C * A ∷ [] ⊢
             app (fst var) (snd var)
               [ ext ! ([ product ⇒ product ] (abs (f [ ext ! (pair (var [ weaken ]) var)])) × var) ]
           ≡
             f
      eval-comp = trans comm/app (trans (cong/app (trans comm/fst (cong/fst (var/ext _ _))) (trans comm/snd (cong/snd (var/ext _ _)))) (trans (cong/app (trans (beta/*₁ _ _) comm/abs) (beta/*₂ _ _)) (trans (beta/=> _ _) (trans (sym sub/∙) (trans (cong/sub (trans ext∙ (cong/ext (trans (cong/∙ (trans ext∙ (cong/ext (sym !-unique) comm/fst)) refl) (trans ext∙ (cong/ext (sym !-unique) (trans comm/fst (cong/fst (trans (sym sub/∙) (cong/sub weaken/ext refl))))))) (trans (var/ext _ _) (var/ext _ _)))) refl) (trans (sym sub/∙) (trans (cong/sub (trans ext∙ (trans (cong/ext (sym !-unique) (trans comm/pair (cong/pair (trans (sym sub/∙) (trans (cong/sub weaken/ext refl) (trans (var/ext _ _) (cong/fst sub/id)))) (var/ext _ _)))) (trans (cong/ext !-unique (eta/* _)) η-pair))) refl) sub/id)))))))

      open BinaryProducts (record { product = product })
      open Category Cl

      helper : forall {A B C} {f : A ⇒ B => C}
        -> B ∷ A ∷ [] ⊨ ext ! (var [ weaken ]) ≡ weaken
      helper = trans (cong/ext (!-unique {γ = weaken ∙ weaken}) refl) (trans (sym ext∙) (trans (cong/∙ η-pair refl) id∙ˡ))

      curry-unique : forall {A B C} {f : A ⇒ B => C} {g : A × B ⇒ C}
        -> app (fst var) (snd var) ∘ (f ⁂ Category.id Cl) ≈ g
        -> f ≈ abs (g [ ext ! (pair (var [ weaken ]) var) ])
      curry-unique {A} {B} {C} {f = f} {g = g} x =
        begin
          f
        ≈˘⟨ eta/=> _ ⟩
          abs (app (f [ weaken ]) var)
        ≈˘⟨ cong/abs (cong/app (cong/sub (helper {f = f}) refl) refl) ⟩
          abs (app (f [ ext ! (var [ weaken ]) ]) var)
        ≈˘⟨ cong/abs (cong/app (beta/*₁ _ _) (beta/*₂ _ _)) ⟩
          abs (app (fst (pair (f [ ext ! (var [ weaken ]) ]) var)) (snd (pair (f [ ext ! (var [ weaken ]) ]) var)))
        ≈˘⟨ cong/abs (cong/app (trans comm/fst (cong/fst (var/ext _ _))) (trans comm/snd (cong/snd (var/ext _ _)))) ⟩
          abs (app (fst var [ ext ! (pair (f [ ext ! (var [ weaken ]) ]) var) ]) (snd var [ ext ! (pair (f [ ext ! (var [ weaken ]) ]) var) ]))
        ≈˘⟨ cong/abs comm/app ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (var [ weaken ]) ]) var) ])
        ≈˘⟨ cong/abs (cong/sub (cong/ext refl (cong/pair (cong/sub (cong/ext refl (trans comm/fst (trans (cong/fst (var/ext _ _)) (beta/*₁ _ _)))) refl) refl)) refl) ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (fst var [ ext ! (pair (var [ weaken ]) var)]) ]) var) ])
        ≈˘⟨ cong/abs (cong/sub (cong/ext refl (cong/pair (cong/sub (trans ext∙ (cong/ext (sym !-unique) refl)) refl) (trans (cong/snd (var/ext _ _)) (beta/*₂ _ _)))) refl) ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (fst var) ∙ ext ! (pair (var [ weaken ]) var) ]) (snd (var [ ext ! (pair (var [ weaken ]) var) ]))) ])
        ≈˘⟨ cong/abs (cong/sub (cong/ext refl (cong/pair (sym sub/∙) comm/snd)) refl) ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (fst var) ] [ ext ! (pair (var [ weaken ]) var) ]) (snd var [ ext ! (pair (var [ weaken ]) var) ])) ])
        ≈˘⟨ cong/abs (cong/sub (cong/ext refl comm/pair) refl) ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (fst var) ]) (snd var) [ ext ! (pair (var [ weaken ]) var) ]) ])
        ≈⟨ cong/abs (cong/sub (cong/ext !-unique (cong/sub refl (cong/pair refl (sym (var/ext _ _))))) refl) ⟩
          abs (app (fst var) (snd var) [ ext (! ∙ ext ! (pair (var [ weaken ]) var)) (pair (f [ ext ! (fst var) ]) (var [ ext ! (snd var) ]) [ ext ! (pair (var [ weaken ]) var) ]) ])
        ≈˘⟨ cong/abs (cong/sub ext∙ refl) ⟩
          abs (app (fst var) (snd var) [ ext ! (pair (f [ ext ! (fst var) ]) (var [ ext ! (snd var) ])) ∙ ext ! (pair (var [ weaken ]) var) ])
        ≡⟨⟩
          abs (app (fst var) (snd var) [ ext ! ⟨ f ∘ fst var , Category.id Cl ∘ snd var ⟩ ∙ ext ! (pair (var [ weaken ]) var) ])
        ≈⟨ cong/abs sub/∙ ⟩
          abs ((app (fst var) (snd var) ∘ ⟨ f ∘ fst var , Category.id Cl ∘ snd var ⟩) [ ext ! (pair (var [ weaken ]) var) ])
        ≡⟨⟩
          abs ((app (fst var) (snd var) ∘ (f ⁂ Category.id Cl)) [ ext ! (pair (var [ weaken ]) var) ])
        ≈⟨ cong/abs (cong/sub refl x) ⟩
          abs (g [ ext ! (pair (var [ weaken ]) var) ])
        ∎
        where
          open import Relation.Binary.Reasoning.Setoid TermSetoid

open import Categories.Category.CartesianClosed Cl
import Categories.Category.CartesianClosed.Canonical Cl as Can

CC : CartesianClosed
CC = Can.Equivalence.fromCanonical M.CC

open import Semantics Cl CC Sg
open Category Cl

private
  open import Data.Product using (_,_)

  open import Categories.Morphism Cl using (Iso; _≅_)
  open import Categories.Category.Cartesian using (Cartesian)
  open import Categories.Functor
  open import Categories.Functor.Properties using ([_]-resp-∘)
  open import Categories.Functor.Construction.Product using (Product)
  open import Categories.Functor.Construction.Exponential using (Exp)
  open import Categories.Functor.Bifunctor using (Bifunctor)

  open CartesianClosed CC
  open BinaryProducts (Cartesian.products cartesian)
  open I ⌊_⌋

  P : Bifunctor Cl Cl Cl
  P = Product Cl cartesian

  E : Bifunctor Cl op Cl
  E = Exp Cl CC

  from/⟦⟧T : forall (A : Type) -> ⟦ A ⟧T ⇒ A
  to/⟦⟧T : forall (A : Type) -> A ⇒ ⟦ A ⟧T

  from/⟦⟧T ⌊ x ⌋ = Category.id Cl
  from/⟦⟧T Unit = Category.id Cl
  from/⟦⟧T (A * A₁) = from/⟦⟧T A ⁂ from/⟦⟧T A₁
  from/⟦⟧T (A => A₁) = λg (from/⟦⟧T A₁ ∘ eval′ ∘ (Category.id Cl ⁂ to/⟦⟧T A))

  to/⟦⟧T ⌊ x ⌋ = Category.id Cl
  to/⟦⟧T Unit = Category.id Cl
  to/⟦⟧T (A * A₁) = to/⟦⟧T A ⁂ to/⟦⟧T A₁
  to/⟦⟧T (A => A₁) = λg (to/⟦⟧T A₁ ∘ eval′ ∘ (Category.id Cl ⁂ from/⟦⟧T A))

  to∘from : forall {A} -> ⟦ A ⟧T ∷ [] ⊢ to/⟦⟧T A [ ext ! (from/⟦⟧T A) ] ≡ var
  to∘from {⌊ x ⌋} = var/ext _ _
  to∘from {Unit} = var/ext _ _
  to∘from {A * A₁} = trans ([ P ]-resp-∘ (to∘from , to∘from)) (Functor.identity P)
  to∘from {A => A₁} = trans ([ E ]-resp-∘ (to∘from , to∘from)) (Functor.identity E)

  from∘to : forall {A} -> A ∷ [] ⊢ from/⟦⟧T A [ ext ! (to/⟦⟧T A) ] ≡ var
  from∘to {⌊ x ⌋} = var/ext _ _
  from∘to {Unit} = var/ext _ _
  from∘to {A * A₁} = trans ([ P ]-resp-∘ (from∘to , from∘to)) (Functor.identity P)
  from∘to {A => A₁} = trans ([ E ]-resp-∘ (from∘to , from∘to)) (Functor.identity E)

  Iso/⟦⟧T : forall {A : Type} -> ⟦ A ⟧T ≅ A
  Iso/⟦⟧T {A} = record
    { from = from/⟦⟧T A
    ; to = to/⟦⟧T A
    ; iso = record { isoˡ = to∘from ; isoʳ = from∘to }
    }

  ⟦_⟧F : (f : Func) -> ⟦ dom f ⟧T ⇒ ⟦ cod f ⟧T
  ⟦_⟧F f = _≅_.to Iso/⟦⟧T ∘ x ∘ _≅_.from Iso/⟦⟧T
    where
      x : dom f ⇒ cod f
      x = func f var

S : Structure
S = record { ⟦_⟧G = ⌊_⌋ ; ⟦_⟧F = λ f → ⟦ f ⟧F }

open Structure S

private
  γC : forall {Γ} -> ⟦ Γ ⟧C ∷ [] ⊨ Γ
  γC {[]} = !
  γC {A ∷ Γ} = ext (γC {Γ} ∙ ext ! π₁) (from/⟦⟧T A ∘ π₂)

  open HomReasoning
  open import Categories.Morphism.Reasoning Cl
  import Categories.Object.Product Cl as Prod

  helper : forall {Γ} {A} {e : Γ ⊢ A} -> ⟦ e ⟧ ≈ to/⟦⟧T A ∘ (e [ γC ])
  helperS : forall {Γ Γ′} {γ : Γ ⊨ Γ′} -> _ ⊨ γC ∙ ext ! ⟦ γ ⟧S ≡ γ ∙ γC

  helper {e = func f e} =
    begin
      (to/⟦⟧T (cod f) ∘ func f var ∘ from/⟦⟧T (dom f)) ∘ ⟦ e ⟧
    ≈⟨ ∘-resp-≈ʳ (helper {e = e}) ⟩
      (to/⟦⟧T (cod f) ∘ func f var ∘ from/⟦⟧T (dom f)) ∘ to/⟦⟧T _ ∘ (e [ γC ])
    ≈⟨ assoc²' ⟩
      to/⟦⟧T (cod f) ∘ func f var ∘ from/⟦⟧T (dom f) ∘ to/⟦⟧T (dom f) ∘ (e [ γC ])
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (cancelˡ from∘to)) ⟩
      to/⟦⟧T (cod f) ∘ func f var ∘ (e [ γC ])
    ≈⟨ ∘-resp-≈ʳ (comm/func _ _ _ _ _) ⟩
      to/⟦⟧T (cod f) ∘ func f (var ∘ (e [ γC ]))
    ≈⟨ ∘-resp-≈ʳ (cong/func identityˡ) ⟩
      to/⟦⟧T (cod f) ∘ func f (e [ γC ])
    ≈˘⟨ ∘-resp-≈ʳ (comm/func _ _ _ _ _) ⟩
      to/⟦⟧T (cod f) ∘ (func f e [ γC ])
    ∎
  helper {e = var} =
    begin
      π₂
    ≈⟨ insertˡ to∘from ⟩
      to/⟦⟧T _ ∘ (from/⟦⟧T _ ∘ π₂)
    ≈˘⟨ ∘-resp-≈ʳ (var/ext _ _) ⟩
      to/⟦⟧T _ ∘ (var [ ext _ (from/⟦⟧T _ ∘ π₂) ])
    ∎
  helper {e = unit} = T.!-unique _
  helper {e = pair e₁ e₂} =
    begin
      ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
    ≈⟨ ⟨⟩-cong₂ (helper {e = e₁}) (helper {e = e₂}) ⟩
      ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩
    ≈˘⟨ ⁂∘⟨⟩ ⟩
      (to/⟦⟧T _ ⁂ to/⟦⟧T _) ∘ (pair (e₁ [ γC ]) (e₂ [ γC ]))
    ≈˘⟨ ∘-resp-≈ʳ comm/pair ⟩
      (to/⟦⟧T _ ⁂ to/⟦⟧T _) ∘ (pair e₁ e₂ [ γC ])
    ∎
  helper {e = fst {A = A} {B = B} e} = switch-fromtoˡ Iso/⟦⟧T (
    begin
      from/⟦⟧T _ ∘ π₁ ∘ ⟦ e ⟧
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (helper {e = e})) ⟩
      from/⟦⟧T A ∘ π₁ ∘ to/⟦⟧T (A * B) ∘ (e [ γC ])
    ≈⟨ ∘-resp-≈ʳ (pullˡ π₁∘⁂) ⟩
      from/⟦⟧T A ∘ (to/⟦⟧T A ∘ π₁) ∘ (e [ γC ])
    ≈⟨ assoc²'' ⟩
      (from/⟦⟧T A ∘ to/⟦⟧T A) ∘ π₁ ∘ (e [ γC ])
    ≈⟨ elimˡ from∘to ⟩
      π₁ ∘ (e [ γC ])
    ≈⟨ comm/fst ⟩
      fst (var [ ext ! (e [ γC ]) ])
    ≈⟨ cong/fst (var/ext _ _) ⟩
      fst (e [ γC ])
    ≈˘⟨ comm/fst ⟩
      fst e [ γC ]
    ∎)
  helper {e = snd e} =
    begin
      π₂ ∘ ⟦ e ⟧
    ≈⟨ ∘-resp-≈ʳ (helper {e = e}) ⟩
      π₂ ∘ (to/⟦⟧T _ ∘ (e [ γC ]))
    ≈⟨ pullˡ π₂∘⁂ ⟩
      (to/⟦⟧T _ ∘ snd var) ∘ (e [ γC ])
    ≈⟨ pullʳ comm/snd ⟩
      to/⟦⟧T _ ∘ snd (var ∘ (e [ γC ]))
    ≈⟨ ∘-resp-≈ʳ (cong/snd identityˡ) ⟩
      to/⟦⟧T _ ∘ snd (e [ γC ])
    ≈˘⟨ ∘-resp-≈ʳ comm/snd ⟩
      to/⟦⟧T _ ∘ (snd e [ γC ])
    ∎
  helper {e = abs e} =
    begin
      λg ⟦ e ⟧
    ≈⟨ λ-cong (helper {e = e}) ⟩
      λg (to/⟦⟧T _ ∘ (e [ γC ]))
    ≈⟨ refl ⟩
      λg (to/⟦⟧T _ ∘ (e [ ext (γC ∙ ext ! π₁) (from/⟦⟧T _ ∘ π₂) ]))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (cong/sub (cong/ext id∙ʳ refl) refl)) ⟩
      λg (to/⟦⟧T _ ∘ (e [ ext ((γC ∙ ext ! π₁) ∙ _⊨_.id) (from/⟦⟧T _ ∘ π₂) ]))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (cong/sub ×id′-ext refl)) ⟩
      λg (to/⟦⟧T _ ∘ (e [ (γC ∙ ext ! π₁) ×id′ ∙ ext _⊨_.id (from/⟦⟧T _ ∘ π₂)]))
    ≈⟨ λ-cong (∘-resp-≈ʳ sub/∙) ⟩
      λg (to/⟦⟧T _ ∘ (e [ (γC ∙ ext ! π₁) ×id′ ] [ ext _⊨_.id (from/⟦⟧T _ ∘ π₂)]))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (cong/sub refl (cong/sub ×id′-∙ refl))) ⟩
      λg (to/⟦⟧T _ ∘ (e [ γC ×id′ ∙ ext ! π₁ ×id′ ] [ ext _⊨_.id (from/⟦⟧T _ ∘ π₂)]))
    ≈⟨ λ-cong (∘-resp-≈ʳ (cong/sub refl sub/∙)) ⟩
      λg (to/⟦⟧T _ ∘ (e [ ext (γC ∙ weaken) var ] [ ext (ext ! π₁ ∙ weaken) var ] [ ext _⊨_.id (from/⟦⟧T _ ∘ π₂)]))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (beta/=> _ _)) ⟩
      λg (to/⟦⟧T _ ∘ app (abs (e [ ext (γC ∙ weaken) var ] [ ext (ext ! π₁ ∙ weaken) var ])) (from/⟦⟧T _ ∘ π₂))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (cong/app comm/abs refl)) ⟩
      λg (to/⟦⟧T _ ∘ app (abs (e [ ext (γC ∙ weaken) var ]) ∘ π₁) (from/⟦⟧T _ ∘ π₂))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (cong/app (beta/*₁ _ _) (beta/*₂ _ _))) ⟩
      λg (to/⟦⟧T _ ∘ app (fst (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _)) (snd (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _)))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (trans comm/app (cong/app (trans comm/fst (cong/fst (var/ext _ _))) (trans comm/snd (cong/snd (var/ext _ _)))))) ⟩
      λg (to/⟦⟧T _ ∘ (app π₁ π₂) ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ˡ (cong/app (beta/*₁ _ _) (beta/*₂ _ _)))) ⟩
      λg (to/⟦⟧T _ ∘ (app (fst (pair π₁ π₂)) (snd (pair π₁ π₂))) ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ˡ (cong/app (trans comm/fst (cong/fst (var/ext _ _))) (trans comm/snd (cong/snd (var/ext _ _)))))) ⟩
      λg (to/⟦⟧T _ ∘ (app (fst var ∘ pair π₁ π₂) (snd var ∘ pair π₁ π₂)) ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ˡ comm/app)) ⟩
      λg (to/⟦⟧T _ ∘ (app (fst var) (snd var) ∘ (pair π₁ π₂)) ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈⟨ refl ⟩
      λg (to/⟦⟧T _ ∘ (eval ∘ Prod.repack product exp.product) ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈⟨ refl ⟩
      λg (to/⟦⟧T _ ∘ eval′ ∘ (abs (e [ ext (γC ∙ weaken) var ]) ⁂ from/⟦⟧T _))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ comm/abs refl))) ⟩
      λg (to/⟦⟧T _ ∘ eval′ ∘ ((abs e [ γC ]) ⁂ from/⟦⟧T _))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityˡ (Category.identityʳ Cl)))) ⟩
      λg (to/⟦⟧T _ ∘ eval′ ∘ (var ∘ (abs e [ γC ]) ⁂ from/⟦⟧T _ ∘ var))
    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
      λg (to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _) ∘ ((abs e [ γC ]) ⁂ var))
    ≈˘⟨ λ-cong assoc²' ⟩
      λg ((to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) ∘ ((abs e [ γC ]) ⁂ var))
    ≈˘⟨ exp.subst product product ⟩
      (λg (to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _))) ∘ (abs e [ γC ])
    ≈⟨ refl ⟩
      to/⟦⟧T (_ => _) ∘ (abs e [ γC ])
    ∎
  helper {e = app e₁ e₂} =
    begin
      eval′ ∘ ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
    ≈⟨ refl ⟩
      (app (fst var) (snd var) ∘ _) ∘ ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
    ≈⟨ ∘-resp-≈ˡ (elimʳ η) ⟩
      app (fst var) (snd var) ∘ ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
    ≈⟨ ∘-resp-≈ʳ (⟨⟩-cong₂ (helper {e = e₁}) (helper {e = e₂})) ⟩
      app (fst var) (snd var) ∘ ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩
    ≈⟨ comm/app ⟩
      app (fst var ∘ ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩)
          (snd var ∘ ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩)
    ≈⟨ cong/app comm/fst comm/snd ⟩
      app (fst (var ∘ ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩))
          (snd (var ∘ ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩))
    ≈⟨ cong/app (cong/fst (var/ext _ _)) (cong/snd (var/ext _ _)) ⟩
      app (fst ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩)
          (snd ⟨ to/⟦⟧T _ ∘ (e₁ [ γC ]) , to/⟦⟧T _ ∘ (e₂ [ γC ]) ⟩)
    ≈⟨ cong/app (beta/*₁ _ _) (beta/*₂ _ _) ⟩
      app (to/⟦⟧T (_ => _) ∘ (e₁ [ γC ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ refl ⟩
      app (λg (to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) ∘ (e₁ [ γC ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ refl ⟩
      app (curry ((to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) ∘ Prod.repack product product) ∘ (e₁ [ γC ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ refl ⟩
      app (abs (((to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) ∘ Prod.repack product product) [ ext ! (pair (var [ weaken ]) var) ]) ∘ (e₁ [ γC ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ cong/app (cong/sub refl (cong/abs (cong/sub refl (elimʳ η)))) refl ⟩
      app (abs ((to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ]) ∘ (e₁ [ γC ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ cong/app comm/abs refl ⟩
      app (abs ((to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext ! (e₁ [ γC ]) ×id′ ]))
          (to/⟦⟧T _ ∘ (e₂ [ γC ]))
    ≈⟨ beta/=> _ _ ⟩
      (to/⟦⟧T _ ∘ eval′ ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext ! (e₁ [ γC ]) ×id′ ] [ ext _⊨_.id (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈⟨ refl ⟩
      (to/⟦⟧T _ ∘ (eval ∘ Prod.repack product product) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext ! (e₁ [ γC ]) ×id′ ] [ ext _⊨_.id (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈⟨ cong/sub refl (cong/sub refl (cong/sub refl (∘-resp-≈ʳ (∘-resp-≈ˡ (elimʳ η))))) ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext ! (e₁ [ γC ]) ×id′ ] [ ext _⊨_.id (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈˘⟨ sub/∙ ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext ! (e₁ [ γC ]) ×id′ ∙ ext _⊨_.id (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈⟨ cong/sub (×id′-ext) refl ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext (ext ! (e₁ [ γC ]) ∙ _⊨_.id) (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈⟨ cong/sub (cong/ext id∙ʳ refl) refl ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ] [ ext (ext ! (e₁ [ γC ])) (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈˘⟨ sub/∙ ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) [ ext ! (pair (var [ weaken ]) var) ∙ ext (ext ! (e₁ [ γC ])) (to/⟦⟧T _ ∘ (e₂ [ γC ])) ]
    ≈⟨ cong/sub (trans ext∙ (cong/ext (sym !-unique) refl)) refl ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) ∘ (pair (var [ weaken ]) var [ ext (ext ! (e₁ [ γC ])) (to/⟦⟧T _ ∘ (e₂ [ γC ])) ])
    ≈⟨ ∘-resp-≈ʳ (trans comm/pair (cong/pair (trans (sym sub/∙) (cong/sub weaken/ext refl)) (var/ext _ _))) ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) ∘ (pair (var [ (ext ! (e₁ [ γC ])) ]) (to/⟦⟧T _ ∘ (e₂ [ γC ])))
    ≈⟨ ∘-resp-≈ʳ (cong/pair (var/ext _ _) refl) ⟩
      (to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (var ⁂ from/⟦⟧T _)) ∘ (pair (e₁ [ γC ]) (to/⟦⟧T _ ∘ (e₂ [ γC ])))
    ≈⟨ pull-last ⁂∘⟨⟩ ⟩
      to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (pair (var ∘ (e₁ [ γC ])) (from/⟦⟧T _ ∘ to/⟦⟧T _ ∘ (e₂ [ γC ])))
    ≈⟨ ∘-resp-≈ʳ (cong/sub (cong/ext refl (cong/pair identityˡ (cancelˡ from∘to))) refl) ⟩
      to/⟦⟧T _ ∘ (app (fst var) (snd var)) ∘ (pair (e₁ [ γC ]) (e₂ [ γC ]))
    ≈⟨ ∘-resp-≈ʳ (trans comm/app (cong/app (trans comm/fst (trans (cong/fst (var/ext _ _)) (beta/*₁ _ _))) (trans comm/snd (trans (cong/snd (var/ext _ _)) (beta/*₂ _ _))))) ⟩
      to/⟦⟧T _ ∘ (app (e₁ [ γC ]) (e₂ [ γC ]))
    ≈˘⟨ ∘-resp-≈ʳ (comm/app) ⟩
      to/⟦⟧T _ ∘ (app e₁ e₂ [ γC ])
    ∎
      where
        curry : _ -> _
        curry e = abs (e [ ext ! (pair (var [ weaken ]) var) ])
  helper {e = e [ γ ]} =
    begin
      ⟦ e ⟧ ∘ ⟦ γ ⟧S
    ≈⟨ pushˡ (helper {e = e}) ⟩
      to/⟦⟧T _ ∘ (e [ γC ]) ∘ ⟦ γ ⟧S
    ≈⟨ refl ⟩
      to/⟦⟧T _ ∘ (e [ γC ] [ ext ! ⟦ γ ⟧S ])
    ≈˘⟨ ∘-resp-≈ʳ sub/∙ ⟩
      to/⟦⟧T _ ∘ (e [ γC ∙ ext ! ⟦ γ ⟧S ])
    ≈⟨ ∘-resp-≈ʳ (cong/sub (helperS {γ = γ}) refl) ⟩
      to/⟦⟧T _ ∘ (e [ γ ∙ γC ])
    ≈⟨ ∘-resp-≈ʳ sub/∙ ⟩
      to/⟦⟧T _ ∘ (e [ γ ] [ γC ])
    ∎

  helperS {γ = id} = trans (trans (cong/∙ refl (cong/ext !-unique refl)) (trans (cong/∙ refl η-pair) id∙ʳ)) (sym id∙ˡ)
  helperS {γ = γ ∙ γ₁} =
    S.begin
      γC ∙ ext ! (⟦ γ ⟧S ∘ ⟦ γ₁ ⟧S)
    S.≈˘⟨ cong/∙ refl (trans ext∙ (cong/ext (sym !-unique) refl)) ⟩
      γC ∙ (ext ! ⟦ γ ⟧S ∙ ext ! ⟦ γ₁ ⟧S)
    S.≈˘⟨ assoc∙ ⟩
      (γC ∙ ext ! ⟦ γ ⟧S) ∙ ext ! ⟦ γ₁ ⟧S
    S.≈⟨ cong/∙ (helperS {γ = γ}) refl ⟩
      (γ ∙ γC) ∙ ext ! ⟦ γ₁ ⟧S
    S.≈⟨ assoc∙ ⟩
      γ ∙ (γC ∙ ext ! ⟦ γ₁ ⟧S)
    S.≈⟨ cong/∙ refl (helperS {γ = γ₁}) ⟩
      γ ∙ (γ₁ ∙ γC)
    S.≈˘⟨ assoc∙ ⟩
      (γ ∙ γ₁) ∙ γC
    S.∎
    where import Relation.Binary.Reasoning.Setoid SubstSetoid as S
  helperS {γ = weaken} = sym weaken/ext
  helperS {γ = ext γ e} =
    S.begin
      γC {_ ∷ _} ∙ (ext ! ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩)
    S.≡⟨⟩
      ext (γC ∙ ext ! π₁) (from/⟦⟧T _ ∘ π₂) ∙ (ext ! ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩)
    S.≈⟨ ext∙ ⟩
      ext ((γC ∙ ext ! π₁) ∙ (ext ! ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩)) ((from/⟦⟧T _ ∘ π₂) ∘ ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩)
    S.≈⟨ cong/ext assoc∙ (pullʳ project₂) ⟩
      ext (γC ∙ (ext ! π₁ ∙ (ext ! ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩))) (from/⟦⟧T _ ∘ ⟦ e ⟧)
    S.≈⟨ cong/ext (cong/∙ refl (trans ext∙ (cong/ext (sym !-unique) refl))) refl ⟩
      ext (γC ∙ (ext ! (π₁ [ ext ! ⟨ ⟦ γ ⟧S , ⟦ e ⟧ ⟩ ]))) (from/⟦⟧T _ ∘ ⟦ e ⟧)
    S.≈⟨ cong/ext (cong/∙ refl (cong/ext refl project₁)) refl ⟩
      ext (γC ∙ ext ! ⟦ γ ⟧S) (from/⟦⟧T _ ∘ ⟦ e ⟧)
    S.≈⟨ cong/ext (helperS {γ = γ}) (sym (switch-tofromˡ Iso/⟦⟧T (sym (helper {e = e})))) ⟩
      ext (γ ∙ γC) (e [ γC ])
    S.≈˘⟨ ext∙ ⟩
      ext γ e ∙ γC
    S.∎
    where import Relation.Binary.Reasoning.Setoid SubstSetoid as S
  helperS {γ = !} = trans (sym !-unique) !-unique

  satisfyAxiom : forall {Γ} {A} {e₁ e₂ : Γ ⊢ A} -> Ax Γ A e₁ e₂ -> ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
  satisfyAxiom {Γ} {A} {e₁} {e₂} x = trans (helper {e = e₁}) (trans (∘-resp-≈ʳ a) (sym (helper { e = e₂})))
    where
      a : (e₁ [ γC ]) ≈ (e₂ [ γC ])
      a = cong/sub refl (ax x)

M : Model Cl CC Th
M = S , satisfyAxiom
