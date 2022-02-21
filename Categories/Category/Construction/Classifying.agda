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

      open import Categories.Category.BinaryProducts Cl
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
