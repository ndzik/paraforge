{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.WeightTying where

-- Weight tying is a restriction of an untied parameterized layer. The 2-cell
-- points from the untied source to the tied target, while its G.1 parameter
-- map points backwards by copying one tied parameter into both source slots.

open import Level using (Level)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization

-- The diagonal embeds a shared parameter into two independent slots.
copyParameter :
  ∀ {p : Level} {P : Set p} → P → P × P
copyParameter parameter = parameter , parameter

-- Restrict an evaluator with two independent parameters to the diagonal.
tieEvaluator :
  ∀ {o p : Level} {A B : Set o} {P : Set p} →
  ((P × P) × A → B) → P × A → B
tieEvaluator evaluator (parameter , input) =
  evaluator (copyParameter parameter , input)

untiedLayer :
  ∀ {o p : Level} {A B : Set o} {P : Set p} →
  ((P × P) × A → B) → Para {o = o} {p = p} A B
untiedLayer {P = P} evaluator = mkPara (P × P) evaluator

tiedLayer :
  ∀ {o p : Level} {A B : Set o} {P : Set p} →
  ((P × P) × A → B) → Para {o = o} {p = p} A B
tiedLayer {P = P} evaluator = mkPara P (tieEvaluator evaluator)

tiePreserves :
  ∀ {o p : Level} {A B : Set o} {P : Set p} →
  (evaluator : (P × P) × A → B) →
  ∀ parameter input →
  run (tiedLayer evaluator) (parameter , input) ≡
  run (untiedLayer evaluator) (copyParameter parameter , input)
tiePreserves evaluator parameter input = refl

-- The cell direction is untied ⇒ tied; mapParameters has the required
-- opposite direction P → P × P.
untiedToTied :
  ∀ {o p : Level} {A B : Set o} {P : Set p} →
  (evaluator : (P × P) × A → B) →
  Reparameterization (untiedLayer evaluator) (tiedLayer evaluator)
untiedToTied evaluator =
  mkReparameterization copyParameter (tiePreserves evaluator)

-- A finite example: the source layer has two independently chosen biases.
twoBiasEvaluator : (ℕ × ℕ) × ℕ → ℕ
twoBiasEvaluator ((firstBias , secondBias) , input) =
  firstBias + (secondBias + input)

untiedTwoBiasLayer : Para ℕ ℕ
untiedTwoBiasLayer = untiedLayer twoBiasEvaluator

tiedTwoBiasLayer : Para ℕ ℕ
tiedTwoBiasLayer = tiedLayer twoBiasEvaluator

twoBiasWeightTying :
  Reparameterization untiedTwoBiasLayer tiedTwoBiasLayer
twoBiasWeightTying = untiedToTied twoBiasEvaluator

copy-evaluates : mapParameters twoBiasWeightTying 3 ≡ (3 , 3)
copy-evaluates = refl

tied-layer-evaluates : run tiedTwoBiasLayer (3 , 4) ≡ 10
tied-layer-evaluates = refl

weight-tying-preserves :
  run tiedTwoBiasLayer (3 , 4) ≡
  run untiedTwoBiasLayer (mapParameters twoBiasWeightTying 3 , 4)
weight-tying-preserves = preserves-run twoBiasWeightTying 3 4
