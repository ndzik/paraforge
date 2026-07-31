{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ActegoryWeightTying where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import ParaForge.Para.Set as Concrete
import ParaForge.Para.Set.Reparameterization as ConcreteCells
import ParaForge.Para.Actegory as General
import ParaForge.Para.Actegory.Reparameterization as GeneralCells
import ParaForge.Para.Actegory.Restriction as Restriction
import ParaForge.Para.Actegory.Sharing as Sharing
open import ParaForge.Para.Actegory.Instance.Sets
  using
    ( Sets-Actegory; Sets-ParameterComonoid
    ; toConcrete; toConcreteCell
    )
open import ParaForge.Examples.WeightTying
  using
    ( twoBiasEvaluator; untiedTwoBiasLayer; tiedTwoBiasLayer
    ; twoBiasWeightTying
    )
import ParaForge.Recurrence.Fold as Fold

private
  Sets₀-Actegory = Sets-Actegory {o = 0ℓ}
  ℕ-Comonoid = Sets-ParameterComonoid ℕ

-- The general actegory construction computes the same two-slot source and
-- diagonal restriction as the concrete executable model.
actegoryUntiedTwoBiasLayer : General.Para Sets₀-Actegory ℕ ℕ
actegoryUntiedTwoBiasLayer =
  Sharing.untiedParameterPair ℕ twoBiasEvaluator

actegoryTiedTwoBiasLayer : General.Para Sets₀-Actegory ℕ ℕ
actegoryTiedTwoBiasLayer =
  Sharing.tieParameterPair ℕ-Comonoid twoBiasEvaluator

actegoryTwoBiasWeightTying :
  GeneralCells.Reparameterization
    Sets₀-Actegory
    actegoryUntiedTwoBiasLayer
    actegoryTiedTwoBiasLayer
actegoryTwoBiasWeightTying =
  Sharing.tieParameterPairCell ℕ-Comonoid twoBiasEvaluator

actegory-copy-evaluates :
  GeneralCells.mapParameters actegoryTwoBiasWeightTying 3 ≡ (3 , 3)
actegory-copy-evaluates = refl

actegory-tied-layer-evaluates :
  General.run actegoryTiedTwoBiasLayer (3 , 4) ≡ 10
actegory-tied-layer-evaluates = refl

actegory-weight-tying-preserves :
  General.run actegoryTiedTwoBiasLayer (3 , 4) ≡
  General.run actegoryUntiedTwoBiasLayer
    (GeneralCells.mapParameters actegoryTwoBiasWeightTying 3 , 4)
actegory-weight-tying-preserves =
  GeneralCells.preserves-run actegoryTwoBiasWeightTying (3 , 4)

actegory-untied-recovers-concrete :
  Concrete.run (toConcrete actegoryUntiedTwoBiasLayer) ((2 , 3) , 4) ≡
  Concrete.run untiedTwoBiasLayer ((2 , 3) , 4)
actegory-untied-recovers-concrete = refl

actegory-tied-recovers-concrete :
  Concrete.run (toConcrete actegoryTiedTwoBiasLayer) (3 , 4) ≡
  Concrete.run tiedTwoBiasLayer (3 , 4)
actegory-tied-recovers-concrete = refl

translatedTwoBiasWeightTying :
  ConcreteCells.Reparameterization
    (toConcrete actegoryUntiedTwoBiasLayer)
    (toConcrete actegoryTiedTwoBiasLayer)
translatedTwoBiasWeightTying =
  toConcreteCell actegoryTwoBiasWeightTying

actegory-cell-recovers-concrete :
  ConcreteCells._≈_
    translatedTwoBiasWeightTying
    twoBiasWeightTying
actegory-cell-recovers-concrete parameter = refl

-- Three-way sharing uses the library's normalized left-associated parameter
-- tensor. The existing finite fold uses a right-associated product, so the
-- evaluator performs that reassociation explicitly.
foldTripleEvaluator :
  (((ℕ × ℕ) × ℕ) × Vec.Vec ℕ 2) → ℕ
foldTripleEvaluator (((first , second) , third) , inputs) =
  Fold.foldUntiedEvaluator Fold.sumCell 2
    ((first , (second , third)) , inputs)

actegoryUntiedFold :
  General.Para Sets₀-Actegory (Vec.Vec ℕ 2) ℕ
actegoryUntiedFold =
  Sharing.untiedParameterTriple ℕ foldTripleEvaluator

actegorySharedFold :
  General.Para Sets₀-Actegory (Vec.Vec ℕ 2) ℕ
actegorySharedFold =
  Sharing.tieParameterTriple ℕ-Comonoid foldTripleEvaluator

actegorySharedFoldAlternative :
  General.Para Sets₀-Actegory (Vec.Vec ℕ 2) ℕ
actegorySharedFoldAlternative =
  Sharing.tieParameterTripleAlternative ℕ-Comonoid foldTripleEvaluator

actegoryFoldTying :
  GeneralCells.Reparameterization
    Sets₀-Actegory
    actegoryUntiedFold
    actegorySharedFold
actegoryFoldTying =
  Restriction.restrictCell
    actegoryUntiedFold
    (Sharing.copyParameter3ˡ ℕ-Comonoid)

actegory-fold-copy-evaluates :
  GeneralCells.mapParameters actegoryFoldTying 1 ≡ ((1 , 1) , 1)
actegory-fold-copy-evaluates = refl

rightAssociate : ∀ {P : Set} → ((P × P) × P) → P × (P × P)
rightAssociate ((first , second) , third) =
  first , (second , third)

actegory-fold-copy-recovers-concrete :
  rightAssociate (GeneralCells.mapParameters actegoryFoldTying 1) ≡
  ConcreteCells.mapParameters Fold.sumFoldTying 1
actegory-fold-copy-recovers-concrete = refl

actegory-fold-shared-evaluates :
  General.run actegorySharedFold (1 , Fold.sampleVector) ≡ 8
actegory-fold-shared-evaluates = refl

actegory-fold-recovers-concrete :
  General.run actegorySharedFold (1 , Fold.sampleVector) ≡
  Concrete.run (Fold.foldSharedAt Fold.sumCell 2)
    (1 , Fold.sampleVector)
actegory-fold-recovers-concrete = refl

actegory-fold-sharing-preserves :
  General.run actegorySharedFold (1 , Fold.sampleVector) ≡
  General.run actegoryUntiedFold
    (GeneralCells.mapParameters actegoryFoldTying 1 , Fold.sampleVector)
actegory-fold-sharing-preserves =
  GeneralCells.preserves-run actegoryFoldTying (1 , Fold.sampleVector)

actegory-fold-copy-trees-agree :
  General.run actegorySharedFold (1 , Fold.sampleVector) ≡
  General.run actegorySharedFoldAlternative (1 , Fold.sampleVector)
actegory-fold-copy-trees-agree =
  Sharing.tieParameterTriple-run-coherent
    {𝒜 = Sets₀-Actegory}
    ℕ-Comonoid foldTripleEvaluator
    (1 , Fold.sampleVector)
