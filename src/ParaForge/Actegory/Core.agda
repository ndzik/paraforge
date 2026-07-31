{-# OPTIONS --safe --without-K #-}

module ParaForge.Actegory.Core where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Properties as MonoidalProperties
open import Categories.Category.Product
  using (Product; _⁂_; assocˡ)
open import Categories.Functor
  using (Functor; id; _∘F_)
open import Categories.Functor.Bifunctor using (appˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; niHelper)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- A left actegory separates the monoidal category of parameters from the
-- category of computations. Unit and associativity are natural isomorphisms;
-- triangle and pentagon make their interaction with the parameter tensor
-- explicit.
record Actegory
  {M : Category oₘ ℓₘ eₘ}
  (V : Monoidal M)
  (𝒞 : Category o𝒞 ℓ𝒞 e𝒞) :
  Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V

  field
    action : Functor (Product M 𝒞) 𝒞

  module action = Functor action

  infixr 10 _⊙₀_ _⊙₁_

  _⊙₀_ : M.Obj → 𝒞.Obj → 𝒞.Obj
  P ⊙₀ A = action.F₀ (P , A)

  _⊙₁_ :
    ∀ {P Q : M.Obj} {A B : 𝒞.Obj} →
    P M.⇒ Q → A 𝒞.⇒ B → (P ⊙₀ A) 𝒞.⇒ (Q ⊙₀ B)
  p ⊙₁ f = action.F₁ (p , f)

  -- Functors compared by the action unit isomorphism, I ⊙ - ≅ Id.
  unitAction : Functor 𝒞 𝒞
  unitAction = appˡ action V.unit

  -- Functors compared by action associativity,
  -- (P ⊗ Q) ⊙ A ≅ P ⊙ (Q ⊙ A).
  tensorAction : Functor (Product (Product M M) 𝒞) 𝒞
  tensorAction = action ∘F (V.⊗ ⁂ id)

  nestedAction : Functor (Product (Product M M) 𝒞) 𝒞
  nestedAction =
    action ∘F ((id ⁂ action) ∘F assocˡ M M 𝒞)

  field
    unitor : NaturalIsomorphism unitAction id
    associator : NaturalIsomorphism tensorAction nestedAction

  module unitor = NaturalIsomorphism unitor
  module associator = NaturalIsomorphism associator

  field
    -- This is the left-unit coherence consequence used by the left Para
    -- unitor. It is derivable from the standard actegory axioms, but storing
    -- it explicitly keeps downstream evaluator proofs independent of a full
    -- actegory coherence theorem.
    unitorˡ-coherence :
      ∀ {P : M.Obj} {A : 𝒞.Obj} →
      (unitor.⇒.η (P ⊙₀ A) 𝒞.∘
        associator.⇒.η ((V.unit , P) , A))
        𝒞.≈
      (V.unitorˡ.from ⊙₁ 𝒞.id)

    triangle :
      ∀ {P : M.Obj} {A : 𝒞.Obj} →
      ((M.id ⊙₁ unitor.⇒.η A) 𝒞.∘
        associator.⇒.η ((P , V.unit) , A))
        𝒞.≈
      (V.unitorʳ.from ⊙₁ 𝒞.id)

    pentagon :
      ∀ {P Q R : M.Obj} {A : 𝒞.Obj} →
      ((M.id ⊙₁ associator.⇒.η ((Q , R) , A)) 𝒞.∘
        associator.⇒.η ((P , Q V.⊗₀ R) , A) 𝒞.∘
        (V.associator.from ⊙₁ 𝒞.id))
        𝒞.≈
      (associator.⇒.η ((P , Q) , R ⊙₀ A) 𝒞.∘
        associator.⇒.η ((P V.⊗₀ Q , R) , A))

open Actegory public

-- Tensor is the canonical action of a monoidal category on itself. This is the
-- reference instance that the general Para construction must recover.
tensorSelfAction :
  ∀ {𝒞 : Category o𝒞 ℓ𝒞 e𝒞} (V : Monoidal 𝒞) →
  Actegory V 𝒞
tensorSelfAction {𝒞 = 𝒞} V = record
  { action = V.⊗
  ; unitor = niHelper record
      { η = λ _ → V.unitorˡ.from
      ; η⁻¹ = λ _ → V.unitorˡ.to
      ; commute = λ _ → V.unitorˡ-commute-from
      ; iso = λ _ → V.unitorˡ.iso
      }
  ; associator = niHelper record
      { η = λ _ → V.associator.from
      ; η⁻¹ = λ _ → V.associator.to
      ; commute = λ _ → V.assoc-commute-from
      ; iso = λ _ → V.associator.iso
      }
  ; unitorˡ-coherence = MonoidalProperties.coherence₁ V
  ; triangle = V.triangle
  ; pentagon = V.pentagon
  }
  where
    module V = Monoidal V
