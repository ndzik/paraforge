{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.Reparameterization where

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization
open import ParaForge.Examples.Composition using (addParameter)

-- This is interesting since reparameterization relates two layers with the
-- same input and output types by translating only their parameters.
-- It is important to realize that it CANNOT introduce behavior that the
-- original layer family F could not already express.
-- Depending on the reparameterization `r` this can represent:
-- * Coordinate changes
-- * Parameter constraints: r selects a restricted family
-- * Weight tying: r(p) = (p, p)
-- * Redudnant parameterizations: several p' values map to the same p.
-- * Discard parameters: r ignores part of p'.
-- The example below directly reflects that. The cell maps `n → 2n`, so
-- the target layer expresses only the even-offset members of the original
-- addition family!
-- In short: We can think of reparamterization more of restrictions. They do
-- not express new behaviors, only represent existing ones (either restricted or
-- redundant).

double : ℕ → ℕ
double n = n + n

-- This target family can express only the even offsets of addParameter.
doubleOffsetEvaluator : ℕ × ℕ → ℕ
doubleOffsetEvaluator (parameter , input) = double parameter + input

doubleOffset : Para ℕ ℕ
doubleOffset = mkPara ℕ doubleOffsetEvaluator

doubleOffsetPreserves : ∀ parameter input →
  run doubleOffset (parameter , input) ≡
  run addParameter (double parameter , input)
doubleOffsetPreserves parameter input = refl

-- G.1 direction: addParameter ⇒ doubleOffset carries the backwards map
-- from a target parameter to the corresponding source parameter.
doubleOffsetCell : Reparameterization addParameter doubleOffset
doubleOffsetCell = mkReparameterization double doubleOffsetPreserves

quadrupleOffsetEvaluator : ℕ × ℕ → ℕ
quadrupleOffsetEvaluator (parameter , input) =
  double (double parameter) + input

quadrupleOffset : Para ℕ ℕ
quadrupleOffset = mkPara ℕ quadrupleOffsetEvaluator

quadrupleOffsetPreserves : ∀ parameter input →
  run quadrupleOffset (parameter , input) ≡
  run doubleOffset (double parameter , input)
quadrupleOffsetPreserves parameter input = refl

quadrupleOffsetCell : Reparameterization doubleOffset quadrupleOffset
quadrupleOffsetCell =
  mkReparameterization double quadrupleOffsetPreserves

-- Vertical composition follows target-to-source maps:
-- quadrupleOffset → doubleOffset → addParameter.
compositeCell : Reparameterization addParameter quadrupleOffset
compositeCell = quadrupleOffsetCell ∘ᵥ doubleOffsetCell

map-direction-evaluates :
  mapParameters doubleOffsetCell 3 ≡ 6
map-direction-evaluates = refl

vertical-map-evaluates :
  mapParameters compositeCell 3 ≡ 12
vertical-map-evaluates = refl

vertical-composite-preserves :
  run quadrupleOffset (3 , 4) ≡
  run addParameter (mapParameters compositeCell 3 , 4)
vertical-composite-preserves = preserves-run compositeCell 3 4

vertical-left-identity :
  (id₂ ∘ᵥ doubleOffsetCell) ≈ doubleOffsetCell
vertical-left-identity = ∘ᵥ-identityˡ doubleOffsetCell

vertical-right-identity :
  (doubleOffsetCell ∘ᵥ id₂) ≈ doubleOffsetCell
vertical-right-identity = ∘ᵥ-identityʳ doubleOffsetCell
