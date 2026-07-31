{-# OPTIONS --safe --without-K #-}

module ParaForge.Actegory.Strong.Monad where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Monad using (Monad)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Endofunctor
  using (Strength; StrongEndofunctor)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- A strong monad on the computation category of an actegory. The Monad field
-- reuses agda-categories' functor, unit, multiplication, and monad laws. The
-- existing Strength contributes joint naturality plus AS1/AS2; the two fields
-- below are precisely AS3/AS4.
record StrongMonad
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  (𝒜 : Actegory V 𝒞) :
  Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module 𝒜 = Actegory 𝒜

  field
    monad : Monad 𝒞

  module monad = Monad monad

  field
    strength : Strength 𝒜 monad.F

  open Strength strength public

  field
    -- AS3: strength commutes with monad multiplication.
    multiplication-coherence :
      ∀ {P : M.Obj} {A : 𝒞.Obj} →
      (monad.μ.η (P 𝒜.⊙₀ A) 𝒞.∘
        monad.F.F₁ (σ P A) 𝒞.∘
        σ P (monad.F.F₀ A))
        𝒞.≈
      (σ P A 𝒞.∘
        (M.id 𝒜.⊙₁ monad.μ.η A))

    -- AS4: strength commutes with the monad unit.
    monad-unit-coherence :
      ∀ {P : M.Obj} {A : 𝒞.Obj} →
      (σ P A 𝒞.∘
        (M.id 𝒜.⊙₁ monad.η.η A))
        𝒞.≈
      monad.η.η (P 𝒜.⊙₀ A)

-- Forgetting AS3/AS4 recovers exactly the Phase 20 structure.
strongEndofunctor :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M}
    {𝒜 : Actegory V 𝒞} →
  StrongMonad 𝒜 → StrongEndofunctor 𝒜
strongEndofunctor S = record
  { F = StrongMonad.monad.F S
  ; strength = StrongMonad.strength S
  }

open StrongMonad public
