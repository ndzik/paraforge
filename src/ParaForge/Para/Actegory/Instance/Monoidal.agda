{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Instance.Monoidal where

open import Level using (Level; _⊔_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (tensorSelfAction)
import ParaForge.Para.Actegory as General
import ParaForge.Para.Actegory.Reparameterization as GeneralCells
import ParaForge.Para.Actegory.Bicategory as GeneralBicategory
import ParaForge.Para.Monoidal as Self
import ParaForge.Para.Monoidal.Reparameterization as SelfCells
import ParaForge.Para.Monoidal.Bicategory as SelfBicategory

private
  variable
    o ℓ e : Level

module _ {𝒞 : Category o ℓ e} (V : Monoidal 𝒞) where

  private
    module 𝒞 = Category 𝒞
    module V = Monoidal V

  open 𝒞 using (Obj)

  private
    variable
      A B D : Obj

  -- The actegory bicategory instantiated with tensor has exactly the same
  -- universe signature as the Milestone 2 self-action bicategory.
  SelfActionPara : Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e o
  SelfActionPara =
    GeneralBicategory.ParaActegory (tensorSelfAction V)

  MonoidalPara : Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e o
  MonoidalPara = SelfBicategory.ParaMonoidal V

  -- The two 1-cell records have the same computational components. Explicit
  -- translations avoid claiming equality of complete bicategory records.
  toMonoidal :
    General.Para (tensorSelfAction V) A B →
    Self.Para V A B
  toMonoidal F = Self.mkPara
    (General.Parameters F)
    (General.run F)

  fromMonoidal :
    Self.Para V A B →
    General.Para (tensorSelfAction V) A B
  fromMonoidal F = General.mkPara
    (Self.Parameters F)
    (Self.run F)

  toMonoidal-run :
    (F : General.Para (tensorSelfAction V) A B) →
    Self.run (toMonoidal F) 𝒞.≈ General.run F
  toMonoidal-run F = 𝒞.Equiv.refl

  fromMonoidal-run :
    (F : Self.Para V A B) →
    General.run (fromMonoidal F) 𝒞.≈ Self.run F
  fromMonoidal-run F = 𝒞.Equiv.refl

  -- G.1 orientation is preserved definitionally: both translations retain the
  -- same target-to-source parameter morphism.
  toMonoidalCell :
    ∀ {F G : General.Para (tensorSelfAction V) A B} →
    GeneralCells.Reparameterization (tensorSelfAction V) F G →
    SelfCells.Reparameterization V (toMonoidal F) (toMonoidal G)
  toMonoidalCell α = SelfCells.mkReparameterization
    (GeneralCells.mapParameters α)
    (GeneralCells.preserves-run α)

  fromMonoidalCell :
    ∀ {F G : Self.Para V A B} →
    SelfCells.Reparameterization V F G →
    GeneralCells.Reparameterization
      (tensorSelfAction V)
      (fromMonoidal F)
      (fromMonoidal G)
  fromMonoidalCell α = GeneralCells.mkReparameterization
    (SelfCells.mapParameters α)
    (SelfCells.preserves-run α)

  to-from-cell-map :
    ∀ {F G : Self.Para V A B}
      (α : SelfCells.Reparameterization V F G) →
    SelfCells._≈_
      (toMonoidalCell (fromMonoidalCell α))
      α
  to-from-cell-map α = 𝒞.Equiv.refl

  from-to-cell-map :
    ∀ {F G : General.Para (tensorSelfAction V) A B}
      (α : GeneralCells.Reparameterization (tensorSelfAction V) F G) →
    GeneralCells._≈_
      (fromMonoidalCell (toMonoidalCell α))
      α
  from-to-cell-map α = 𝒞.Equiv.refl

  identity-agrees :
    ∀ {A : Obj} →
    Self.run
      (toMonoidal
        (General.idₚ {𝒜 = tensorSelfAction V} {A = A}))
      𝒞.≈
    Self.run (Self.idₚ {M = V} {A = A})
  identity-agrees = 𝒞.Equiv.refl

  -- Both constructions compose with Q ⊗ P, and their evaluator paths agree
  -- definitionally under the translation.
  composition-agrees :
    (G : General.Para (tensorSelfAction V) B D) →
    (F : General.Para (tensorSelfAction V) A B) →
    Self.run (toMonoidal (General._∘ₚ_ G F)) 𝒞.≈
      Self.run (Self._∘ₚ_ (toMonoidal G) (toMonoidal F))
  composition-agrees G F = 𝒞.Equiv.refl

  identity-cell-agrees :
    (F : General.Para (tensorSelfAction V) A B) →
    SelfCells._≈_
      (toMonoidalCell (GeneralCells.id₂ {F = F}))
      (SelfCells.id₂ {F = toMonoidal F})
  identity-cell-agrees F = 𝒞.Equiv.refl

  vertical-composition-agrees :
    ∀ {F G H : General.Para (tensorSelfAction V) A B}
      (β : GeneralCells.Reparameterization (tensorSelfAction V) G H)
      (α : GeneralCells.Reparameterization (tensorSelfAction V) F G) →
    SelfCells._≈_
      (toMonoidalCell (GeneralCells._∘ᵥ_ β α))
      (SelfCells._∘ᵥ_ (toMonoidalCell β) (toMonoidalCell α))
  vertical-composition-agrees β α = 𝒞.Equiv.refl

  horizontal-composition-agrees :
    ∀ {F F′ : General.Para (tensorSelfAction V) A B}
      {G G′ : General.Para (tensorSelfAction V) B D}
      (β : GeneralCells.Reparameterization (tensorSelfAction V) G G′)
      (α : GeneralCells.Reparameterization (tensorSelfAction V) F F′) →
    SelfCells._≈_
      (toMonoidalCell (GeneralCells._∘ₕ_ β α))
      (SelfCells._∘ₕ_ (toMonoidalCell β) (toMonoidalCell α))
  horizontal-composition-agrees β α = 𝒞.Equiv.refl
