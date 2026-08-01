{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Strong.LaxAlgebra.Comonoid where

open import Level using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Monad using (StrongMonad)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Restriction
open import ParaForge.Para.Actegory.Sharing
  using
    ( ParameterComonoid
    ; untiedParameterPair; tieParameterPair; tieParameterPairCell
    )
open import ParaForge.Para.Actegory.Strong.LaxAlgebra

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
    module 𝒜 = Actegory 𝒜

  private
    variable
      A B X : 𝒞.Obj

  -- Weak form of Theorem G.10. Phase 25 has already normalized the raw
  -- G.1 maps along the right unitor:
  --
  --   P ⊗ I ⇒ I      becomes  P ⇒ I
  --   P ⊗ I ⇒ P ⊗ P becomes  P ⇒ P ⊗ P.
  --
  -- The three lax coherence equations are exactly the IsMonoid laws in the
  -- monoidal opposite, so no additional parameter structure is assumed.
  laxAlgebraParameterComonoid :
    {A : 𝒞.Obj} (𝔄 : LaxAlgebra S A) →
    ParameterComonoid V (Parameters (structure 𝔄))
  laxAlgebraParameterComonoid 𝔄 = record
    { μ = algebraCopy 𝔄
    ; η = algebraDiscard 𝔄
    ; assoc = lax-associativity 𝔄
    ; identityˡ = lax-unitˡ 𝔄
    ; identityʳ = lax-unitʳ 𝔄
    }

  extractedDiscard-agrees :
    {A : 𝒞.Obj} (𝔄 : LaxAlgebra S A) →
    ParaForge.Para.Actegory.Sharing.discardParameter
      (laxAlgebraParameterComonoid 𝔄)
      M.≈ algebraDiscard 𝔄
  extractedDiscard-agrees 𝔄 = M.Equiv.refl

  extractedCopy-agrees :
    {A : 𝒞.Obj} (𝔄 : LaxAlgebra S A) →
    ParaForge.Para.Actegory.Sharing.copyParameter
      (laxAlgebraParameterComonoid 𝔄)
      M.≈ algebraCopy 𝔄
  extractedCopy-agrees 𝔄 = M.Equiv.refl

  PairEvaluator :
    (𝔄 : LaxAlgebra S X) →
    (A B : 𝒞.Obj) → Set ℓ𝒞
  PairEvaluator 𝔄 A B =
    (((Parameters (structure 𝔄) V.⊗₀
      Parameters (structure 𝔄)) 𝒜.⊙₀ A) 𝒞.⇒ B)

  -- The sharing operation induced by a lax algebra is restriction of an
  -- untied evaluator along the extracted copy map.
  tieLaxParameterPair :
    (𝔄 : LaxAlgebra S X) →
    PairEvaluator 𝔄 A B →
    Para 𝒜 A B
  tieLaxParameterPair 𝔄 f =
    restrictParameters
      (untiedParameterPair (Parameters (structure 𝔄)) f)
      (algebraCopy 𝔄)

  tieLaxParameterPairCell :
    (𝔄 : LaxAlgebra S X) →
    (f : PairEvaluator 𝔄 A B) →
    Reparameterization 𝒜
      (untiedParameterPair (Parameters (structure 𝔄)) f)
      (tieLaxParameterPair 𝔄 f)
  tieLaxParameterPairCell 𝔄 f =
    restrictCell
      (untiedParameterPair (Parameters (structure 𝔄)) f)
      (algebraCopy 𝔄)

  tieLaxParameterPair-agrees :
    (𝔄 : LaxAlgebra S X) →
    (f : PairEvaluator 𝔄 A B) →
    run (tieLaxParameterPair 𝔄 f)
      𝒞.≈
    run (tieParameterPair {𝒜 = 𝒜}
      (laxAlgebraParameterComonoid 𝔄) f)
  tieLaxParameterPair-agrees 𝔄 f = 𝒞.Equiv.refl

  tieLaxParameterPairCell-agrees :
    (𝔄 : LaxAlgebra S X) →
    (f : PairEvaluator 𝔄 A B) →
    tieLaxParameterPairCell 𝔄 f
      ≈ tieParameterPairCell {𝒜 = 𝒜}
          (laxAlgebraParameterComonoid 𝔄) f
  tieLaxParameterPairCell-agrees 𝔄 f = M.Equiv.refl
