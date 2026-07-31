{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Strong.Algebra where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Endofunctor
  using (StrongEndofunctor)
open import ParaForge.Para.Actegory using (Para)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞}
  (S : StrongEndofunctor 𝒜) where

  private
    module 𝒞 = Category 𝒞
    module S = StrongEndofunctor S

  -- An algebra or coalgebra for the endofunctor lifted to Para is a
  -- parameterized structure map. Lax coherence is deliberately not part of
  -- these aliases; it belongs to the later pseudomonad development.
  Algebra : 𝒞.Obj → Set (oₘ ⊔ ℓ𝒞)
  Algebra A = Para 𝒜 (S.F.F₀ A) A

  Coalgebra : 𝒞.Obj → Set (oₘ ⊔ ℓ𝒞)
  Coalgebra A = Para 𝒜 A (S.F.F₀ A)
