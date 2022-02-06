open import Categories.Category
open import Categories.Category.CartesianClosed

open import Theory

module Categories.Category.Instance.Models
  {ℓ₁ ℓ₂ ℓ₃}
  (Th : Theory.Theory ℓ₁ ℓ₂ ℓ₃)
  {o ℓ e}
  (𝒞 : Category o ℓ e)
  (cartesianClosed : CartesianClosed 𝒞)
  where

  open import Categories.Category.Cartesian 𝒞
  open import Categories.Category.BinaryProducts 𝒞
  import Categories.Object.Terminal 𝒞 as T
  import Categories.Object.Product 𝒞 as P
  open import Categories.Morphism 𝒞

  open Category 𝒞
  open CartesianClosed cartesianClosed
  open Cartesian cartesian
  open BinaryProducts products
  open HomReasoning
  open import Categories.Morphism.Reasoning 𝒞

  open import Syntax
  open import Semantics 𝒞 cartesianClosed Th

  open Theory.Theory Th
  open Signature Sg

  open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)

  open import Relation.Binary using (Rel; IsEquivalence)

  open import Level using (_⊔_)

  ⁂-id : forall {A B} -> id {A = A} ⁂ id {A = B} ≈ id
  ⁂-id = Equiv.trans (⟨⟩-cong₂ identityˡ identityˡ) η

  module Homomorphism {M N : Model}
    (h : (g : Gr) -> ⟦ g ⟧G (proj₁ M) ≅ ⟦ g ⟧G (proj₁ N))
    where
    open _≅_
    open Iso

    H : (A : Type) -> ⟦ A ⟧T (proj₁ M) ≅ ⟦ A ⟧T (proj₁ N)
    H ⌊ g ⌋ = h g
    H Unit = T.up-to-iso terminal terminal
    H (A * A₁) = record
      { from = (from (H A)) ⁂ from (H A₁)
      ; to = to (H A) ⁂ to (H A₁)
      ; iso = record
        { isoˡ = Equiv.trans ⁂∘⁂ ( Equiv.trans (⁂-cong₂ (isoˡ (iso (H A))) (isoˡ (iso (H A₁)))) (Equiv.trans (⟨⟩-cong₂ identityˡ identityˡ) η) )
        ; isoʳ = Equiv.trans ⁂∘⁂ ( Equiv.trans (⁂-cong₂ (isoʳ (iso (H A))) (isoʳ (iso (H A₁)))) (Equiv.trans (⟨⟩-cong₂ identityˡ identityˡ) η) )
        }
      }
    H (A => A₁) = record
      { from = λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A)))
      ; to = λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A)))
      ; iso = record
        { isoˡ =
          begin
            λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A)))
            ∘
            λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A)))
          ≈⟨ CartesianClosed.exp.subst cartesianClosed product product ⟩
            λg (
              (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A))) ∘ (λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A))) ⁂ Category.id 𝒞)
            )
          ≈⟨ λ-cong assoc²' ⟩
            λg (
              to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A)) ∘ (λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A))) ⁂ Category.id 𝒞)
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (
              to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ∘ λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A))) ⁂ from (H A) ∘ Category.id 𝒞)
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityˡ identityʳ))) ⟩
            λg (
              to (H A₁) ∘ eval′ ∘ (λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A)))) ⁂ from (H A))
            )
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityʳ identityˡ))) ⟩
            λg (
              to (H A₁) ∘ eval′ ∘ (λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A)))) ∘ Category.id 𝒞 ⁂ Category.id 𝒞 ∘ from (H A))
            )
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (
              to (H A₁) ∘ eval′ ∘ (λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A)))) ⁂ Category.id 𝒞) ∘ (Category.id 𝒞 ⁂ from (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (pullˡ β′)) ⟩
            λg (
              to (H A₁) ∘ (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A)))) ∘ (Category.id 𝒞 ⁂ from (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ assoc²') ⟩
            λg (
              to (H A₁) ∘ from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A))) ∘ (Category.id 𝒞 ⁂ from (H A))
            )
          ≈⟨ λ-cong (pullˡ (isoˡ (iso (H A₁)))) ⟩
            λg (
              Category.id 𝒞 ∘ eval′ ∘ (Category.id 𝒞 ⁂ (to (H A))) ∘ (Category.id 𝒞 ⁂ from (H A))
            )
          ≈⟨ λ-cong identityˡ ⟩
            λg (
              eval′ ∘ (Category.id 𝒞 ⁂ (to (H A))) ∘ (Category.id 𝒞 ⁂ from (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ ⁂∘⁂) ⟩
            λg (
              eval′ ∘ (Category.id 𝒞 ∘ Category.id 𝒞 ⁂ (to (H A)) ∘ from (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (⁂-cong₂ identity² (isoˡ (iso (H A))))) ⟩
            λg (
              eval′ ∘ ⟨ Category.id 𝒞 ∘ π₁ , Category.id 𝒞 ∘ π₂ ⟩
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ identityˡ identityˡ)) ⟩
            λg (
              eval′ ∘ ⟨ π₁ , π₂ ⟩
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ η) ⟩
            λg (
              eval′ ∘ Category.id 𝒞
            )
          ≈⟨ λ-cong identityʳ ⟩
            λg eval′
          ≈⟨ η-id′ ⟩
            Category.id 𝒞
          ∎
        ; isoʳ =
          begin
            λg (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A)))
            ∘
            λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A)))
          ≈⟨ CartesianClosed.exp.subst cartesianClosed product product ⟩
            λg (
              (from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A))) ∘ (λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A))) ⁂ Category.id 𝒞)
            )
          ≈⟨ λ-cong assoc²' ⟩
            λg (
              from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ to (H A)) ∘ (λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A))) ⁂ Category.id 𝒞)
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (
              from (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ∘ λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ from (H A))) ⁂ to (H A) ∘ Category.id 𝒞)
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityˡ identityʳ))) ⟩
            λg (
              from (H A₁) ∘ eval′ ∘ (λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A)))) ⁂ to (H A))
            )
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityʳ identityˡ))) ⟩
            λg (
              from (H A₁) ∘ eval′ ∘ (λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A)))) ∘ Category.id 𝒞 ⁂ Category.id 𝒞 ∘ to (H A))
            )
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (
              from (H A₁) ∘ eval′ ∘ (λg (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A)))) ⁂ Category.id 𝒞) ∘ (Category.id 𝒞 ⁂ to (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (pullˡ β′)) ⟩
            λg (
              from (H A₁) ∘ (to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A)))) ∘ (Category.id 𝒞 ⁂ to (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ assoc²') ⟩
            λg (
              from (H A₁) ∘ to (H A₁) ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A))) ∘ (Category.id 𝒞 ⁂ to (H A))
            )
          ≈⟨ λ-cong (pullˡ (isoʳ (iso (H A₁)))) ⟩
            λg (
              Category.id 𝒞 ∘ eval′ ∘ (Category.id 𝒞 ⁂ (from (H A))) ∘ (Category.id 𝒞 ⁂ to (H A))
            )
          ≈⟨ λ-cong identityˡ ⟩
            λg (
              eval′ ∘ (Category.id 𝒞 ⁂ (from (H A))) ∘ (Category.id 𝒞 ⁂ to (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ ⁂∘⁂) ⟩
            λg (
              eval′ ∘ (Category.id 𝒞 ∘ Category.id 𝒞 ⁂ (from (H A)) ∘ to (H A))
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (⁂-cong₂ identity² (isoʳ (iso (H A))))) ⟩
            λg (
              eval′ ∘ ⟨ Category.id 𝒞 ∘ π₁ , Category.id 𝒞 ∘ π₂ ⟩
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ identityˡ identityˡ)) ⟩
            λg (
              eval′ ∘ ⟨ π₁ , π₂ ⟩
            )
          ≈⟨ λ-cong (∘-resp-≈ʳ η) ⟩
            λg (
              eval′ ∘ Category.id 𝒞
            )
          ≈⟨ λ-cong identityʳ ⟩
            λg eval′
          ≈⟨ η-id′ ⟩
            Category.id 𝒞
          ∎
        }
      }

  record homomorphism (M N : Model) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ ⊔ e) where
    field
      h : (g : Gr) -> ⟦ g ⟧G (proj₁ M) ≅ ⟦ g ⟧G (proj₁ N)

    open Homomorphism {M} {N} h public

    field
      comm : (f : Func) -> _≅_.from (H (cod f)) ∘ ⟦ f ⟧F (proj₁ M) ≈ ⟦ f ⟧F (proj₁ N) ∘ _≅_.from (H (dom f))

  module _ {M N : Model} where
    _≗_ : Rel (homomorphism M N) (ℓ₁ ⊔ e)
    _≗_ x y = (g : Gr) -> _≅_.from (homomorphism.h x g) ≈ _≅_.from (homomorphism.h y g)

  module Id {M : Model} where
    open Homomorphism {M} {M} (λ _ → IsEquivalence.refl ≅-isEquivalence)
    open Structure (proj₁ M)

    -- The components of the homomorphism generated by identity morphisms are also identities.
    H-id : forall A -> _≅_.from (H A) ≈ Category.id 𝒞
    H-id˘ : forall A -> _≅_.to (H A) ≈ Category.id 𝒞

    H-id ⌊ x ⌋ = Equiv.refl
    H-id Unit = T.!-unique (Category.id 𝒞)
    H-id (A * A₁) =
      begin
        _≅_.from (H A) ⁂ _≅_.from (H A₁)
      ≈⟨ ⁂-cong₂ (H-id A) (H-id A₁) ⟩
        Category.id 𝒞 ⁂ Category.id 𝒞
      ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
        ⟨ π₁ , π₂ ⟩
      ≈⟨ η ⟩
        Category.id 𝒞
      ∎
    H-id (A => A₁) =
      begin
        λg (_≅_.from (H A₁) ∘ eval′ ∘ (id ⁂ _≅_.to (H A)))
      ≈⟨ λ-cong (∘-resp-≈ˡ (H-id A₁)) ⟩
        λg (id ∘ eval′ ∘ (id ⁂ _≅_.to (H A)))
      ≈⟨ λ-cong (pullˡ identityˡ) ⟩
        λg (eval′ ∘ (id ⁂ _≅_.to (H A)))
      ≈⟨ λ-cong (∘-resp-≈ʳ (⁂-cong₂ Equiv.refl (H-id˘ A))) ⟩
        λg (eval′ ∘ (id ⁂ id))
      ≈⟨ λ-cong (elimʳ ⁂-id) ⟩
        λg eval′
      ≈⟨ η-id′ ⟩
        id
      ∎

    H-id˘ ⌊ x ⌋ = Equiv.refl
    H-id˘ Unit = T.!-unique id
    H-id˘ (A * A₁) =
      begin
        _≅_.to (H A) ⁂ _≅_.to (H A₁)
      ≈⟨ ⁂-cong₂ (H-id˘ A) (H-id˘ A₁) ⟩
        id ⁂ id
      ≈⟨ ⁂-id ⟩
        id
      ∎
    H-id˘ (A => A₁) =
      begin
        λg (_≅_.to (H A₁) ∘ eval′ ∘ (id ⁂ _≅_.from (H A)))
      ≈⟨ λ-cong (elimˡ (H-id˘ A₁)) ⟩
        λg (eval′ ∘ (id ⁂ _≅_.from (H A)))
      ≈⟨ λ-cong (∘-resp-≈ʳ (⁂-cong₂ Equiv.refl (H-id A))) ⟩
        λg (eval′ ∘ (id ⁂ id))
      ≈⟨ λ-cong (elimʳ ⁂-id) ⟩
        λg eval′
      ≈⟨ η-id′ ⟩
        id
      ∎

    comm : (f : Func) -> _≅_.from (H (cod f)) ∘ ⟦ f ⟧F ≈ ⟦ f ⟧F ∘ _≅_.from (H (dom f))
    comm f =
      begin
        _≅_.from (H (cod f)) ∘ ⟦ f ⟧F
      ≈⟨ elimˡ (H-id (cod f)) ⟩
        ⟦ f ⟧F
      ≈˘⟨ elimʳ (H-id (dom f)) ⟩
        ⟦ f ⟧F ∘ _≅_.from (H (dom f))
      ∎

    id′ : homomorphism M M
    id′ = record { h = λ _ → IsEquivalence.refl ≅-isEquivalence ; comm = comm }

  module Compose {M N O : Model} where
    open _≅_

    compose : homomorphism N O -> homomorphism M N -> homomorphism M O
    compose x y = record
      { h = h
      ; comm = λ f →
          begin
            from (MO.H (cod f)) ∘ ⟦ f ⟧F (proj₁ M)
          ≈⟨ pushˡ (H-compose (cod f)) ⟩
            from (NO.H (cod f)) ∘ from (MN.H (cod f)) ∘ ⟦ f ⟧F (proj₁ M)
          ≈⟨ ∘-resp-≈ʳ (MN.comm f) ⟩
            from (NO.H (cod f)) ∘ ⟦ f ⟧F (proj₁ N) ∘ from (MN.H (dom f))
          ≈⟨ pullˡ (NO.comm f) ⟩
            (⟦ f ⟧F (proj₁ O) ∘ from (NO.H (dom f))) ∘ from (MN.H (dom f))
          ≈˘⟨ pushʳ (H-compose (dom f)) ⟩
            ⟦ f ⟧F (proj₁ O) ∘ from (MO.H (dom f))
          ∎
      }
      where
        h = λ g → IsEquivalence.trans ≅-isEquivalence (homomorphism.h y g) (homomorphism.h x g)
        module MO = Homomorphism h
        module MN = homomorphism y
        module NO = homomorphism x

        H-compose : forall A -> from (MO.H A) ≈ from (NO.H A) ∘ from (MN.H A)
        H-compose˘ : forall A -> to (MO.H A) ≈ to (MN.H A) ∘ to (NO.H A)

        H-compose ⌊ x ⌋ = Equiv.refl
        H-compose Unit = T.!-unique₂
        H-compose (A * A₁) = Equiv.trans (⁂-cong₂ (H-compose A) (H-compose A₁)) (Equiv.sym ⁂∘⁂)
        H-compose (A => A₁) =
          begin
            λg (from (MO.H A₁) ∘ eval′ ∘ (id ⁂ to (MO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ˡ (H-compose A₁)) ⟩
            λg ((from (NO.H A₁) ∘ from (MN.H A₁)) ∘ eval′ ∘ (id ⁂ to (MO.H A)))
          ≈⟨ λ-cong assoc ⟩
            λg (from (NO.H A₁) ∘ from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ Equiv.refl (H-compose˘ A))))) ⟩
            λg (from (NO.H A₁) ∘ from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A) ∘ to (NO.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ second∘second))) ⟩
            λg (from (NO.H A₁) ∘ from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A)) ∘ (id ⁂ to (NO.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ assoc²') ⟩
            λg (from (NO.H A₁) ∘ (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ∘ (id ⁂ to (NO.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (pullˡ β′)) ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ⁂ id) ∘ (id ⁂ to (NO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ∘ id ⁂ id ∘ to (NO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityʳ identityˡ))) ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ⁂ to (NO.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityˡ identityʳ))) ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (id ∘ λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ⁂ to (NO.H A) ∘ id))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (id ⁂ to (NO.H A)) ∘ (λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ⁂ id))
          ≈˘⟨ λ-cong assoc²' ⟩
            λg ((from (NO.H A₁) ∘ eval′ ∘ (id ⁂ to (NO.H A))) ∘ (λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A))) ⁂ id))
          ≈˘⟨ CartesianClosed.exp.subst cartesianClosed product product ⟩
            λg (from (NO.H A₁) ∘ eval′ ∘ (id ⁂ to (NO.H A))) ∘ λg (from (MN.H A₁) ∘ eval′ ∘ (id ⁂ to (MN.H A)))
          ≈⟨ Equiv.refl ⟩
            from (NO.H (A => A₁)) ∘ from (MN.H (A => A₁))
          ∎

        H-compose˘ ⌊ x ⌋ = Equiv.refl
        H-compose˘ Unit = T.!-unique₂
        H-compose˘ (A * A₁) = Equiv.trans (⁂-cong₂ (H-compose˘ A) (H-compose˘ A₁)) (Equiv.sym ⁂∘⁂)
        H-compose˘ (A => A₁) =
          begin
            λg (to (MO.H A₁) ∘ eval′ ∘ (id ⁂ from (MO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ˡ (H-compose˘ A₁)) ⟩
            λg ((to (MN.H A₁) ∘ to (NO.H A₁)) ∘ eval′ ∘ (id ⁂ from (MO.H A)))
          ≈⟨ λ-cong assoc ⟩
            λg (to (MN.H A₁) ∘ to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (MO.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ Equiv.refl (H-compose A))))) ⟩
            λg (to (MN.H A₁) ∘ to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A) ∘ from (MN.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ second∘second))) ⟩
            λg (to (MN.H A₁) ∘ to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A)) ∘ (id ⁂ from (MN.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ assoc²') ⟩
            λg (to (MN.H A₁) ∘ (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ∘ (id ⁂ from (MN.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (pullˡ β′)) ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ⁂ id) ∘ (id ⁂ from (MN.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ∘ id ⁂ id ∘ from (MN.H A)))
          ≈⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityʳ identityˡ))) ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ⁂ from (MN.H A)))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ identityˡ identityʳ))) ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (id ∘ λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ⁂ from (MN.H A) ∘ id))
          ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ ⁂∘⁂)) ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (id ⁂ from (MN.H A)) ∘ (λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ⁂ id))
          ≈˘⟨ λ-cong assoc²' ⟩
            λg ((to (MN.H A₁) ∘ eval′ ∘ (id ⁂ from (MN.H A))) ∘ (λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A))) ⁂ id))
          ≈˘⟨ CartesianClosed.exp.subst cartesianClosed product product ⟩
            λg (to (MN.H A₁) ∘ eval′ ∘ (id ⁂ from (MN.H A))) ∘ λg (to (NO.H A₁) ∘ eval′ ∘ (id ⁂ from (NO.H A)))
          ≈⟨ Equiv.refl ⟩
            to (MN.H (A => A₁)) ∘ to (NO.H (A => A₁))
          ∎

  Models : Category (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ o ⊔ ℓ ⊔ e) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ ⊔ e) (ℓ₁ ⊔ e)
  Models = record
             { Obj = Model
             ; _⇒_ = homomorphism
             ; _≈_ = _≗_
             ; id = Id.id′
             ; _∘_ = Compose.compose
             ; assoc = λ _ → assoc
             ; sym-assoc = λ _ → sym-assoc
             ; identityˡ = λ _ → identityˡ
             ; identityʳ = λ _ → identityʳ
             ; identity² = λ _ → identity²
             ; equiv = record { refl = λ _ → IsEquivalence.refl equiv ; sym = λ x g → IsEquivalence.sym equiv (x g) ; trans = λ x x₁ g → IsEquivalence.trans equiv (x g) (x₁ g) }
             ; ∘-resp-≈ = λ x x₁ g → ∘-resp-≈ (x g) (x₁ g)
             }
