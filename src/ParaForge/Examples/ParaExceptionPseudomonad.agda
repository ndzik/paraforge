{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ParaExceptionPseudomonad where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_,_)
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
  using (mapParameters)
open import ParaForge.Para.Actegory.Strong.Endofunctor
  using (liftPara)
open import ParaForge.Para.Actegory.Strong.Monad
  using
    ( ParaPseudomonad; liftPseudomonad
    ; unitPara; multiplicationPara
    ; unitSwap; unitNaturality; multiplicationNaturality
    ; leftUnitCoherence; rightUnitCoherence
    ; associativityCoherence
    )

private
  S = ExceptionStrongMonad ℕ

certificate : ParaPseudomonad S
certificate = liftPseudomonad S

unit-component-evaluates :
  General.run (unitPara S ℕ) (tt , 3) ≡ inj₂ 3
unit-component-evaluates = refl

multiplication-outer-failure-evaluates :
  General.run (multiplicationPara S ℕ) (tt , inj₁ 1) ≡ inj₁ 1
multiplication-outer-failure-evaluates = refl

multiplication-inner-failure-evaluates :
  General.run (multiplicationPara S ℕ)
    (tt , inj₂ (inj₁ 2)) ≡ inj₁ 2
multiplication-inner-failure-evaluates = refl

multiplication-success-evaluates :
  General.run (multiplicationPara S ℕ)
    (tt , inj₂ (inj₂ 3)) ≡ inj₂ 3
multiplication-success-evaluates = refl

unit-swap-evaluates :
  unitSwap S ℕ (2 , tt) ≡ (tt , 2)
unit-swap-evaluates = refl

addParameter : General.Para (Sets-Actegory {o = 0ℓ}) ℕ ℕ
addParameter = General.mkPara ℕ λ where
  (parameter , value) → parameter + value

private
  lift₁ : ∀ {A B : Set} →
    General.Para (Sets-Actegory {o = 0ℓ}) A B →
    General.Para (Sets-Actegory {o = 0ℓ}) (ℕ ⊎ A) (ℕ ⊎ B)
  lift₁ = liftPara (strongEndofunctor S)

  lift₂ : ∀ {A B : Set} →
    General.Para (Sets-Actegory {o = 0ℓ}) A B →
    General.Para
      (Sets-Actegory {o = 0ℓ})
      (ℕ ⊎ (ℕ ⊎ A))
      (ℕ ⊎ (ℕ ⊎ B))
  lift₂ K = lift₁ (lift₁ K)

unit-naturality-source-evaluates :
  General.run (unitPara S ℕ General.∘ₚ addParameter)
    ((tt , 2) , 3) ≡ inj₂ 5
unit-naturality-source-evaluates = refl

unit-naturality-target-evaluates :
  General.run (lift₁ addParameter General.∘ₚ unitPara S ℕ)
    ((2 , tt) , 3) ≡ inj₂ 5
unit-naturality-target-evaluates = refl

unit-naturality-map-evaluates :
  mapParameters (unitNaturality S addParameter) (2 , tt)
    ≡ (tt , 2)
unit-naturality-map-evaluates = refl

multiplication-naturality-source-evaluates :
  General.run
    (multiplicationPara S ℕ General.∘ₚ lift₂ addParameter)
    ((tt , 2) , inj₂ (inj₂ 3)) ≡ inj₂ 5
multiplication-naturality-source-evaluates = refl

multiplication-naturality-target-evaluates :
  General.run
    (lift₁ addParameter General.∘ₚ multiplicationPara S ℕ)
    ((2 , tt) , inj₂ (inj₂ 3)) ≡ inj₂ 5
multiplication-naturality-target-evaluates = refl

multiplication-naturality-map-evaluates :
  mapParameters (multiplicationNaturality S addParameter) (2 , tt)
    ≡ (tt , 2)
multiplication-naturality-map-evaluates = refl

left-unit-coherence-evaluates :
  General.run
    (multiplicationPara S ℕ General.∘ₚ
      lift₁ (unitPara S ℕ))
    ((tt , tt) , inj₂ 3) ≡ inj₂ 3
left-unit-coherence-evaluates = refl

right-unit-coherence-evaluates :
  General.run
    (multiplicationPara S ℕ General.∘ₚ
      unitPara S (ℕ ⊎ ℕ))
    ((tt , tt) , inj₂ 3) ≡ inj₂ 3
right-unit-coherence-evaluates = refl

left-unit-map-evaluates :
  mapParameters (leftUnitCoherence S ℕ) tt ≡ (tt , tt)
left-unit-map-evaluates = refl

right-unit-map-evaluates :
  mapParameters (rightUnitCoherence S ℕ) tt ≡ (tt , tt)
right-unit-map-evaluates = refl

associativity-map-evaluates :
  mapParameters (associativityCoherence S ℕ) (tt , tt)
    ≡ (tt , tt)
associativity-map-evaluates = refl
