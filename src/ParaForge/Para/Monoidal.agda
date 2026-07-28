{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

private
  variable
    o ℓ e : Level

-- The self-action of a monoidal category uses tensor for both parameters and
-- data. The equality level e does not occur in raw 1-cells; it first appears
-- in the preservation equations for reparameterizations.
module _ {C : Category o ℓ e} (M : Monoidal C) where

  open Category C using (Obj; _⇒_)
  open Monoidal M using (_⊗₀_)

  record Para (A B : Obj) : Set (o ⊔ ℓ) where
    constructor mkPara
    field
      Parameters : Obj
      run        : Parameters ⊗₀ A ⇒ B

open Para public

-- M is implicit for operations because it is determined by their Para
-- operands. This keeps sequential composition usable as an infix operator.
module _ {C : Category o ℓ e} {M : Monoidal C} where

  open Category C using (Obj; id; _∘_)
  open Monoidal M using
    (unit; _⊗₀_; _⊗₁_; module unitorˡ; module associator)

  private
    variable
      A B D : Obj

  -- The monoidal unit supplies the parameter object. Eliminating its action
  -- on the input uses the forward (I ⊗ A ⇒ A) direction of the left unitor.
  idₚ : Para M A A
  idₚ = mkPara unit unitorˡ.from

  -- Composition follows the concrete Q × P order. Its evaluator is the path
  --
  --   (Q ⊗ P) ⊗ A → Q ⊗ (P ⊗ A) → Q ⊗ B → D.
  infixr 9 _∘ₚ_

  _∘ₚ_ : Para M B D → Para M A B → Para M A D
  g ∘ₚ f = mkPara
    (Parameters g ⊗₀ Parameters f)
    (run g ∘ (id ⊗₁ run f) ∘ associator.from)
