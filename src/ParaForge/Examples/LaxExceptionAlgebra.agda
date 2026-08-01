{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LaxExceptionAlgebra where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

open import ParaForge.Actegory.Strong.Instance.Sets.Monad
  using (ExceptionStrongMonad)
open import ParaForge.Actegory.Strong.Monad
  using (strongEndofunctor)
import ParaForge.Para.Actegory as General
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory)
open import ParaForge.Para.Actegory.Reparameterization
  using
    ( Reparameterization; mkReparameterization
    ; mapParameters
    )
open import ParaForge.Para.Actegory.Strong.Endofunctor
  using (liftPara)
open import ParaForge.Para.Actegory.Strong.Monad
  using (unitPara; multiplicationPara)
open import ParaForge.Para.Actegory.Strong.LaxAlgebra
  using
    ( LaxAlgebra; structure; unitCell; multiplicationCell
    ; algebraDiscard; algebraCopy
    ; identityStructureCell; composeStructureCell
    ; structureCell
    )

private
  Sets₀-Actegory = Sets-Actegory {o = 0ℓ}
  S = ExceptionStrongMonad ℕ

-- The parameter is the fallback value used to interpret an exception.
fallbackStructure : General.Para Sets₀-Actegory (ℕ ⊎ ℕ) ℕ
fallbackStructure = General.mkPara ℕ λ where
  (fallback , inj₁ _) → fallback
  (_ , inj₂ value) → value

fallbackUnitCell : Reparameterization Sets₀-Actegory
  (General.idₚ {𝒜 = Sets₀-Actegory} {A = ℕ})
  (fallbackStructure General.∘ₚ
    unitPara S ℕ)
fallbackUnitCell = mkReparameterization
  (λ _ → tt)
  λ where
    ((_ , tt) , _) → refl

fallbackMultiplicationCell : Reparameterization Sets₀-Actegory
  (fallbackStructure General.∘ₚ
    liftPara (strongEndofunctor S) fallbackStructure)
  (fallbackStructure General.∘ₚ
    multiplicationPara S ℕ)
fallbackMultiplicationCell = mkReparameterization
  (λ where (fallback , tt) → fallback , fallback)
  λ where
    ((_ , tt) , inj₁ _) → refl
    ((_ , tt) , inj₂ (inj₁ _)) → refl
    ((_ , tt) , inj₂ (inj₂ _)) → refl

fallbackAlgebra : LaxAlgebra S ℕ
fallbackAlgebra = record
  { structure = fallbackStructure
  ; unitCell = fallbackUnitCell
  ; multiplicationCell = fallbackMultiplicationCell
  ; lax-unitˡ = λ _ → refl
  ; lax-unitʳ = λ _ → refl
  ; lax-associativity = λ _ → refl
  }

unit-cell-exposes-deletion :
  mapParameters (unitCell fallbackAlgebra) (4 , tt) ≡ tt
unit-cell-exposes-deletion = refl

multiplication-cell-exposes-copying :
  mapParameters (multiplicationCell fallbackAlgebra) (4 , tt)
    ≡ (4 , 4)
multiplication-cell-exposes-copying = refl

normalized-discard-evaluates :
  algebraDiscard fallbackAlgebra 4 ≡ tt
normalized-discard-evaluates = refl

normalized-copy-evaluates :
  algebraCopy fallbackAlgebra 4 ≡ (4 , 4)
normalized-copy-evaluates = refl

fallback-success-evaluates :
  General.run (structure fallbackAlgebra) (4 , inj₂ 7) ≡ 7
fallback-success-evaluates = refl

fallback-failure-evaluates :
  General.run (structure fallbackAlgebra) (4 , inj₁ 7) ≡ 4
fallback-failure-evaluates = refl

identity-cell-swaps-unit-parameter :
  mapParameters
    (structureCell (identityStructureCell S fallbackAlgebra))
    (tt , 4) ≡ (4 , tt)
identity-cell-swaps-unit-parameter = refl

composed-identity-cell-evaluates :
  mapParameters
    (structureCell
      (composeStructureCell S
        (identityStructureCell S fallbackAlgebra)
        (identityStructureCell S fallbackAlgebra)))
    ((tt , tt) , 4) ≡ (4 , (tt , tt))
composed-identity-cell-evaluates = refl
