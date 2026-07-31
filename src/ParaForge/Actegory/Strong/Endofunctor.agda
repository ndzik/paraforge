{-# OPTIONS --safe --without-K #-}

module ParaForge.Actegory.Strong.Endofunctor where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import ParaForge.Actegory.Core using (Actegory)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- The functors compared by an actegorical strength:
--
--   P ⊙ F A  ⟶  F (P ⊙ A).
strengthSource :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M} →
  Actegory V 𝒞 →
  Functor 𝒞 𝒞 →
  Functor (Product M 𝒞) 𝒞
strengthSource 𝒜 F = Actegory.action 𝒜 ∘F (id ⁂ F)

strengthTarget :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M} →
  Actegory V 𝒞 →
  Functor 𝒞 𝒞 →
  Functor (Product M 𝒞) 𝒞
strengthTarget 𝒜 F = F ∘F Actegory.action 𝒜

-- Strength for an endofunctor on the computation category of an actegory.
-- Naturality is joint in the parameter and computation arguments. AS1 and
-- AS2 retain the weak action unitors and associators explicitly.
record Strength
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  (𝒜 : Actegory V 𝒞)
  (F : Functor 𝒞 𝒞) :
  Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module 𝒜 = Actegory 𝒜
    module F = Functor F

  field
    strengthen :
      NaturalTransformation
        (strengthSource 𝒜 F)
        (strengthTarget 𝒜 F)

  module strengthen = NaturalTransformation strengthen

  σ : ∀ (P : M.Obj) (A : 𝒞.Obj) →
      (P 𝒜.⊙₀ F.F₀ A) 𝒞.⇒ F.F₀ (P 𝒜.⊙₀ A)
  σ P A = strengthen.η (P , A)

  field
    -- AS1: strength at the monoidal unit agrees with the action unitor.
    unit-coherence :
      ∀ {A : 𝒞.Obj} →
      (F.F₁ (𝒜.unitor.⇒.η A) 𝒞.∘ σ V.unit A)
        𝒞.≈
      𝒜.unitor.⇒.η (F.F₀ A)

    -- AS2: strengthening by P ⊗ Q agrees with strengthening successively
    -- by Q and then P, modulo the action associator.
    associativity-coherence :
      ∀ {P Q : M.Obj} {A : 𝒞.Obj} →
      (F.F₁ (𝒜.associator.⇒.η ((P , Q) , A)) 𝒞.∘
        σ (P V.⊗₀ Q) A)
        𝒞.≈
      (σ P (Q 𝒜.⊙₀ A) 𝒞.∘
        (M.id 𝒜.⊙₁ σ Q A) 𝒞.∘
        𝒜.associator.⇒.η ((P , Q) , F.F₀ A))

  -- Joint naturality specialized to a parameter map and an identity
  -- computation map, normalized so downstream G.1 proofs see literal
  -- identities rather than F₁ id.
  strength-natural-id :
    ∀ {P Q : M.Obj} {A : 𝒞.Obj} (r : P M.⇒ Q) →
    (σ Q A 𝒞.∘ (r 𝒜.⊙₁ 𝒞.id {A = F.F₀ A}))
      𝒞.≈
    (F.F₁ (r 𝒜.⊙₁ 𝒞.id {A = A}) 𝒞.∘ σ P A)
  strength-natural-id {P = P} {Q = Q} {A = A} r = begin
    σ Q A 𝒞.∘ (r 𝒜.⊙₁ 𝒞.id)
      ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨
        𝒜.action.F-resp-≈ (M.Equiv.refl , F.identity) ⟩
    σ Q A 𝒞.∘ 𝒜.action.F₁ (r , F.F₁ 𝒞.id)
      ≈⟨ strengthen.commute (r , 𝒞.id) ⟩
    F.F₁ (r 𝒜.⊙₁ 𝒞.id) 𝒞.∘ σ P A
      ∎
    where
      open 𝒞.HomReasoning

-- An endofunctor together with actegorical strength. Keeping Strength
-- separate lets a future strong-monad interface reuse the same data.
record StrongEndofunctor
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  (𝒜 : Actegory V 𝒞) :
  Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞) where

  field
    F : Functor 𝒞 𝒞
    strength : Strength 𝒜 F

  module F = Functor F
  open Strength strength public

open StrongEndofunctor public
