{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.MonoidalSets where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import ParaForge.Para.Set as Concrete
import ParaForge.Para.Monoidal as Generic
import ParaForge.Para.Monoidal.Reparameterization as GenericCells
open import ParaForge.Para.Monoidal.Instance.Sets
  using
    ( Sets-Monoidal; toConcrete; fromConcrete; fromConcreteCell
    ; identity-agrees; composition-agrees
    )

open import ParaForge.Examples.Composition
  using (addParameter; scaleParameter)
open import ParaForge.Examples.WeightTying
  using
    ( untiedTwoBiasLayer; tiedTwoBiasLayer; twoBiasWeightTying )

private
  Sets₀-Monoidal = Sets-Monoidal {o = 0ℓ}

-- The concrete executable layers translate directly into the generic
-- self-action at the common universe level.
genericAddParameter : Generic.Para Sets₀-Monoidal ℕ ℕ
genericAddParameter = fromConcrete addParameter

genericScaleParameter : Generic.Para Sets₀-Monoidal ℕ ℕ
genericScaleParameter = fromConcrete scaleParameter

genericIdℕ : Generic.Para Sets₀-Monoidal ℕ ℕ
genericIdℕ = Generic.idₚ

generic-identity-evaluates :
  Generic.run genericIdℕ (tt , 4) ≡ 4
generic-identity-evaluates = refl

identity-specializes :
  Concrete.run (toConcrete genericIdℕ) (tt , 4) ≡
  Concrete.run (Concrete.idₚ {o = 0ℓ} {p = 0ℓ}) (tt , 4)
identity-specializes = identity-agrees (tt , 4)

-- Generic composition retains the concrete Q × P order: scale is the outer
-- layer and therefore receives the first parameter.
generic-composition-evaluates :
  Generic.run
    (Generic._∘ₚ_ genericScaleParameter genericAddParameter)
    ((2 , 3) , 4)
  ≡ 14
generic-composition-evaluates = refl

composition-specializes :
  Concrete.run
      (toConcrete
        (Generic._∘ₚ_ genericScaleParameter genericAddParameter))
      ((2 , 3) , 4)
    ≡ Concrete.run
      (Concrete._∘ₚ_
        (toConcrete genericScaleParameter)
        (toConcrete genericAddParameter))
      ((2 , 3) , 4)
composition-specializes =
  composition-agrees genericScaleParameter genericAddParameter 2 3 4

-- Copying is not part of bare monoidal Para. In cartesian Sets the existing
-- diagonal cell can nevertheless be translated and executed generically.
genericUntiedTwoBiasLayer : Generic.Para Sets₀-Monoidal ℕ ℕ
genericUntiedTwoBiasLayer = fromConcrete untiedTwoBiasLayer

genericTiedTwoBiasLayer : Generic.Para Sets₀-Monoidal ℕ ℕ
genericTiedTwoBiasLayer = fromConcrete tiedTwoBiasLayer

genericTwoBiasWeightTying :
  GenericCells.Reparameterization
    Sets₀-Monoidal
    genericUntiedTwoBiasLayer
    genericTiedTwoBiasLayer
genericTwoBiasWeightTying = fromConcreteCell twoBiasWeightTying

generic-copy-evaluates :
  GenericCells.mapParameters genericTwoBiasWeightTying 3 ≡ (3 , 3)
generic-copy-evaluates = refl

generic-tied-layer-evaluates :
  Generic.run genericTiedTwoBiasLayer (3 , 4) ≡ 10
generic-tied-layer-evaluates = refl

generic-weight-tying-preserves :
  Generic.run genericTiedTwoBiasLayer (3 , 4) ≡
  Generic.run genericUntiedTwoBiasLayer
    (GenericCells.mapParameters genericTwoBiasWeightTying 3 , 4)
generic-weight-tying-preserves =
  GenericCells.preserves-run genericTwoBiasWeightTying (3 , 4)
