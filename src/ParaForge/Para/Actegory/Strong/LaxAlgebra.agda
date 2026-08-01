{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Strong.LaxAlgebra where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Monad
  using (StrongMonad; strongEndofunctor)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Laws
  using
    ( associator; associator⁻¹
    ; unitorˡ; unitorˡ⁻¹; unitorʳ; unitorʳ⁻¹
    )
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Strong.Endofunctor
  using
    ( liftPara; identity-comparison⁻¹
    ; composition-comparison⁻¹
    )
open import ParaForge.Para.Actegory.Strong.Monad
  using (unitPara; multiplicationPara)

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞}
  (S : StrongMonad 𝒜) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module S = StrongMonad S

    lift₁ : ∀ {A B : 𝒞.Obj} →
      Para 𝒜 A B → Para 𝒜 (S.monad.F.F₀ A) (S.monad.F.F₀ B)
    lift₁ = liftPara (strongEndofunctor S)

  -- Definition F.2, oriented according to G.1:
  --
  --   unitCell           : id_A ⇒ a ∘ η_A
  --   multiplicationCell : a ∘ T(a) ⇒ a ∘ μ_A
  --
  -- If Parameters a = P, their backward parameter maps have the shapes
  -- P ⊗ I ⇒ I and P ⊗ I ⇒ P ⊗ P respectively. These are exactly the raw
  -- counit and copying maps used by Theorem G.10.
  rawDiscardParameter :
    ∀ {A : 𝒞.Obj} (a : Para 𝒜 (S.monad.F.F₀ A) A) →
    Reparameterization 𝒜
      (idₚ {𝒜 = 𝒜} {A = A})
      (a ∘ₚ unitPara S A) →
    Parameters a M.⇒ V.unit
  rawDiscardParameter a ε =
    mapParameters ε M.∘ V.unitorʳ.to

  rawCopyParameter :
    ∀ {A : 𝒞.Obj} (a : Para 𝒜 (S.monad.F.F₀ A) A) →
    Reparameterization 𝒜
      (a ∘ₚ lift₁ a)
      (a ∘ₚ multiplicationPara S A) →
    Parameters a M.⇒
      (Parameters a V.⊗₀ Parameters a)
  rawCopyParameter a δ =
    mapParameters δ M.∘ V.unitorʳ.to

  -- Para-specialized normal forms of the lax unity and associativity
  -- diagrams. Cell equality in Para observes only these morphisms in M;
  -- evaluator-preservation proof records are intentionally not compared.
  record LaxAlgebra (A : 𝒞.Obj) :
    Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ ℓ𝒞 ⊔ e𝒞) where
    field
      structure : Para 𝒜 (S.monad.F.F₀ A) A
      unitCell : Reparameterization 𝒜
        (idₚ {𝒜 = 𝒜} {A = A})
        (structure ∘ₚ unitPara S A)
      multiplicationCell : Reparameterization 𝒜
        (structure ∘ₚ lift₁ structure)
        (structure ∘ₚ multiplicationPara S A)

    algebraDiscard : Parameters structure M.⇒ V.unit
    algebraDiscard = rawDiscardParameter structure unitCell

    algebraCopy : Parameters structure M.⇒
      (Parameters structure V.⊗₀ Parameters structure)
    algebraCopy = rawCopyParameter structure multiplicationCell

    field
      lax-unitˡ :
        V.unitorˡ.to M.≈
          ((algebraDiscard V.⊗₁ M.id) M.∘ algebraCopy)
      lax-unitʳ :
        V.unitorʳ.to M.≈
          ((M.id V.⊗₁ algebraDiscard) M.∘ algebraCopy)
      lax-associativity :
        (algebraCopy V.⊗₁ M.id) M.∘ algebraCopy
          M.≈
        (V.associator.to M.∘
          (M.id V.⊗₁ algebraCopy)) M.∘ algebraCopy

  open LaxAlgebra public

  private
    variable
      A B C : 𝒞.Obj

  -- Definition F.3 orientation. For f with parameter R, a structure cell has
  -- backward map R ⊗ P_A ⇒ P_B ⊗ R.
  record LaxAlgebraMorphismCell
    (𝔄 : LaxAlgebra A)
    (𝔅 : LaxAlgebra B)
    (f : Para 𝒜 A B) :
    Set (ℓₘ ⊔ e𝒞) where
    field
      structureCell : Reparameterization 𝒜
        (structure 𝔅 ∘ₚ lift₁ f)
        (f ∘ₚ structure 𝔄)

  open LaxAlgebraMorphismCell public

  -- The structural pair (f, κ) from Definition F.3. In this
  -- Para-specialized presentation the observable content of κ is its
  -- backward parameter map; composition below is the weak bicategorical
  -- pasting of those cells.
  record LaxAlgebraMorphism
    (𝔄 : LaxAlgebra A)
    (𝔅 : LaxAlgebra B) :
    Set (oₘ ⊔ ℓₘ ⊔ ℓ𝒞 ⊔ e𝒞) where
    field
      underlying : Para 𝒜 A B
      algebraCell : LaxAlgebraMorphismCell 𝔄 𝔅 underlying

  open LaxAlgebraMorphism public

  -- The identity structure cell is the canonical weak pasting
  --
  --   a ∘ T(id) ⇒ a ∘ id ⇒ a ⇒ id ∘ a.
  identityStructureCell :
    (𝔄 : LaxAlgebra A) →
    LaxAlgebraMorphismCell 𝔄 𝔄 (idₚ {𝒜 = 𝒜} {A = A})
  identityStructureCell 𝔄 = record
    { structureCell =
        unitorˡ⁻¹ ∘ᵥ
        unitorʳ ∘ᵥ
        (id₂ ∘ₕ
          identity-comparison⁻¹
            (strongEndofunctor S))
    }

  -- Structure-cell composition is the standard weak bicategorical pasting:
  -- expand T(g ∘ f), apply the two structure cells, and reassociate.
  composeStructureCell :
    {𝔄 : LaxAlgebra A}
    {𝔅 : LaxAlgebra B}
    {ℭ : LaxAlgebra C}
    {f : Para 𝒜 A B}
    {g : Para 𝒜 B C} →
    LaxAlgebraMorphismCell 𝔄 𝔅 f →
    LaxAlgebraMorphismCell 𝔅 ℭ g →
    LaxAlgebraMorphismCell 𝔄 ℭ (g ∘ₚ f)
  composeStructureCell {𝔄 = 𝔄} {𝔅 = 𝔅} {ℭ = ℭ}
    {f = f} {g = g} ϕ ψ = record
      { structureCell =
          associator⁻¹ ∘ᵥ
          (id₂ ∘ₕ structureCell ϕ) ∘ᵥ
          associator ∘ᵥ
          (structureCell ψ ∘ₕ id₂) ∘ᵥ
          associator⁻¹ ∘ᵥ
          (id₂ ∘ₕ
            composition-comparison⁻¹
              (strongEndofunctor S) g f)
      }

  identityMorphism :
    (𝔄 : LaxAlgebra A) → LaxAlgebraMorphism 𝔄 𝔄
  identityMorphism 𝔄 = record
    { underlying = idₚ
    ; algebraCell = identityStructureCell 𝔄
    }

  infixr 8 _∘ₐ_

  _∘ₐ_ :
    {𝔄 : LaxAlgebra A}
    {𝔅 : LaxAlgebra B}
    {ℭ : LaxAlgebra C} →
    LaxAlgebraMorphism 𝔅 ℭ →
    LaxAlgebraMorphism 𝔄 𝔅 →
    LaxAlgebraMorphism 𝔄 ℭ
  ψ ∘ₐ ϕ = record
    { underlying = underlying ψ ∘ₚ underlying ϕ
    ; algebraCell = composeStructureCell
        (algebraCell ϕ) (algebraCell ψ)
    }
