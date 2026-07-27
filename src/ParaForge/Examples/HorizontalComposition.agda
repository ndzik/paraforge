{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.HorizontalComposition where

-- Horizontal composition combines local restrictions of sequential layers.
-- Here both an additive inner layer and a multiplicative outer layer are
-- restricted to even parameters, then lifted to one restriction of the whole
-- two-layer computation.

open import Data.Nat.Base using (ℕ; _*_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization
open import ParaForge.Examples.Composition
  using (addParameter; scaleParameter)
open import ParaForge.Examples.Reparameterization
  using (double; doubleOffset; doubleOffsetCell)

-- The target family can express only the even scale factors of the source.
doubleScaleEvaluator : ℕ × ℕ → ℕ
doubleScaleEvaluator (parameter , input) = double parameter * input

doubleScale : Para ℕ ℕ
doubleScale = mkPara ℕ doubleScaleEvaluator

doubleScalePreserves : ∀ parameter input →
  run doubleScale (parameter , input) ≡
  run scaleParameter (double parameter , input)
doubleScalePreserves parameter input = refl

doubleScaleCell : Reparameterization scaleParameter doubleScale
doubleScaleCell =
  mkReparameterization double doubleScalePreserves

unrestrictedComposite : Para ℕ ℕ
unrestrictedComposite = scaleParameter ∘ₚ addParameter

restrictedComposite : Para ℕ ℕ
restrictedComposite = doubleScale ∘ₚ doubleOffset

-- The outer scale restriction and inner offset restriction combine into a
-- cell between their sequential composites.
horizontalRestriction :
  Reparameterization unrestrictedComposite restrictedComposite
horizontalRestriction = doubleScaleCell ∘ₕ doubleOffsetCell

-- Composite parameters are ordered outer first: scale, then offset. Horizontal
-- composition maps each target component through its local backwards map.
horizontal-map-evaluates :
  mapParameters horizontalRestriction (3 , 4) ≡ (6 , 8)
horizontal-map-evaluates = refl

restricted-composite-evaluates :
  run restrictedComposite ((3 , 4) , 5) ≡ 78
restricted-composite-evaluates = refl

horizontal-composite-preserves :
  run restrictedComposite ((3 , 4) , 5) ≡
  run unrestrictedComposite
    (mapParameters horizontalRestriction (3 , 4) , 5)
horizontal-composite-preserves =
  preserves-run horizontalRestriction (3 , 4) 5

-- Horizontal composition with an identity cell restricts only the inner layer.
inner-only-restriction :
  Reparameterization
    (scaleParameter ∘ₚ addParameter)
    (scaleParameter ∘ₚ doubleOffset)
inner-only-restriction =
  id₂ {F = scaleParameter} ∘ₕ doubleOffsetCell

inner-only-map-evaluates :
  mapParameters inner-only-restriction (3 , 4) ≡ (3 , 8)
inner-only-map-evaluates = refl
