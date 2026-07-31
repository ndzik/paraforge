{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory using (Actegory)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- Parameters live in the monoidal category M while interfaces and evaluators
-- live in the acted-on category C.
module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  (𝒜 : Actegory V 𝒞) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module 𝒜 = Actegory 𝒜

  record Para (A B : 𝒞.Obj) : Set (oₘ ⊔ ℓ𝒞) where
    constructor mkPara
    field
      Parameters : M.Obj
      run : (Parameters 𝒜.⊙₀ A) 𝒞.⇒ B

open Para public

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞} where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module 𝒜 = Actegory 𝒜

  private
    variable
      A B D : 𝒞.Obj

  -- The action unit supplies the evaluator I ⊙ A ⇒ A.
  idₚ : Para 𝒜 A A
  idₚ {A = A} = mkPara V.unit (𝒜.unitor.⇒.η A)

  -- Composition retains the G.1 order Q ⊗ P:
  --
  --   (Q ⊗ P) ⊙ A → Q ⊙ (P ⊙ A) → Q ⊙ B → D.
  infixr 9 _∘ₚ_

  _∘ₚ_ : Para 𝒜 B D → Para 𝒜 A B → Para 𝒜 A D
  _∘ₚ_ {A = A} g f = mkPara
    (Parameters g V.⊗₀ Parameters f)
    (run g 𝒞.∘
      (M.id 𝒜.⊙₁ run f) 𝒞.∘
      𝒜.associator.⇒.η
        ((Parameters g , Parameters f) , A))
