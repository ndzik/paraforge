{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LearningNeuralArchitecture where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import ParaForge.Architecture.Model as Neural
open import ParaForge.Architecture.Interpretation
open import ParaForge.Architecture.Core using (binding)
open import ParaForge.Architecture.Wiring using (copyData)
open import ParaForge.Architecture.Builder.Neural
import ParaForge.Architecture.Instance.Sets as Sets
import ParaForge.Architecture.Instance.Symbolic as ExistingSymbolic
import ParaForge.Examples.ArchitectureBuilder as Builder
open import ParaForge.Learning.Architecture.Parameter
open import ParaForge.Learning.Architecture.Model
open import ParaForge.Learning.Architecture.Interpretation
open import ParaForge.Learning.Architecture.Symbolic
open import ParaForge.Learning.Architecture.Instance.Neural

module Learn = InterpretArchitecture NeuralLearningModel
module Describe = DescribeArchitecture NeuralDataflow
module Execute = Interpret Sets.SetsModel
module Existing = Interpret ExistingSymbolic.SymbolicModel

------------------------------------------------------------------------
-- The existing builder terms receive both established and learning models.

mlpLearner = Learn.interpretNetwork Builder.mlp
encoderLearner = Learn.interpretNetwork Builder.encoderBlock
independentTransformerLearner =
  Learn.interpretNetwork Builder.twoIndependentBlocks
sharedTransformerLearner =
  Learn.interpretNetwork Builder.twoSharedBlocks

mlp-forward-agrees :
  evaluateArchitecture mlpLearner
    (5 ∷ᶜ 4 ∷ᶜ []ᶜ) 3 ≡
  Execute.interpretNetwork Builder.mlp
    (5 Neural.∷ₑ 4 Neural.∷ₑ Neural.ε) 3
mlp-forward-agrees = refl

transformer-forward-agrees :
  evaluateArchitecture encoderLearner
    (4 ∷ᶜ 3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 1 ≡
  Execute.interpretNetwork Builder.encoderBlock
    (4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 1
transformer-forward-agrees = refl

shared-transformer-forward-agrees :
  evaluateArchitecture sharedTransformerLearner
    (4 ∷ᶜ 3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 1 ≡
  Execute.interpretNetwork Builder.twoSharedBlocks
    (4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 1
shared-transformer-forward-agrees = refl

------------------------------------------------------------------------
-- Finite sequential composition, independently parameterized or shared.

sequenceLayer : NeuralModule
  (Neural.denseP 3 3 ∷ [])
  (Neural.vector 3)
  (Neural.vector 3)
sequenceLayer = dense 3 3

threeIndependentLayers : NeuralModule
  (Neural.denseP 3 3 ∷ Neural.denseP 3 3 ∷
    Neural.denseP 3 3 ∷ [])
  (Neural.vector 3)
  (Neural.vector 3)
threeIndependentLayers = repeatIndependent 3 sequenceLayer

threeSharedLayers : NeuralModule
  (Neural.denseP 3 3 ∷ [])
  (Neural.vector 3)
  (Neural.vector 3)
threeSharedLayers = repeatSharedNeural 3 sequenceLayer

independentSequenceLearner =
  Learn.interpretNetwork threeIndependentLayers
sharedSequenceLearner = Learn.interpretNetwork threeSharedLayers

independent-sequence-forward-agrees :
  evaluateArchitecture independentSequenceLearner
    (3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 0 ≡
  Execute.interpretNetwork threeIndependentLayers
    (3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 0
independent-sequence-forward-agrees = refl

shared-sequence-forward-agrees :
  evaluateArchitecture sharedSequenceLearner
    (2 ∷ᶜ []ᶜ) 1 ≡
  Execute.interpretNetwork threeSharedLayers
    (2 Neural.∷ₑ Neural.ε) 1
shared-sequence-forward-agrees = refl

independent-sequence-destinations :
  parameterDestinations (binding threeIndependentLayers) ≡
  just 0 ∷ just 1 ∷ just 2 ∷ []
independent-sequence-destinations = refl

shared-sequence-destinations :
  parameterDestinations (binding threeSharedLayers) ≡
  just 0 ∷ just 0 ∷ just 0 ∷ []
shared-sequence-destinations = refl

shared-sequence-aggregation-sites :
  parameterAggregationSites (binding threeSharedLayers) ≡ 0 ∷ 0 ∷ []
shared-sequence-aggregation-sites = refl

------------------------------------------------------------------------
-- Structural traces project to the established symbolic node semantics.

projectNodes :
  List (LearningNode NeuralDataflow) → List ExistingSymbolic.Node
projectNodes [] = []
projectNodes (primitiveNode operation ∷ rest) =
  ExistingSymbolic.primitiveNode operation ∷ projectNodes rest
projectNodes (dataNode wire ∷ rest) =
  ExistingSymbolic.dataWireNode (eraseDataWire wire) ∷ projectNodes rest
projectNodes (parameterNode _ ∷ rest) = projectNodes rest

copyCount : List (LearningNode NeuralDataflow) → ℕ
copyCount [] = zero
copyCount (dataNode copyData ∷ rest) = suc (copyCount rest)
copyCount (_ ∷ rest) = copyCount rest

leftResidualCount : List NeuralFeedbackEvent → ℕ
leftResidualCount [] = zero
leftResidualCount (leftResidual ∷ rest) = suc (leftResidualCount rest)
leftResidualCount (_ ∷ rest) = leftResidualCount rest

rightResidualCount : List NeuralFeedbackEvent → ℕ
rightResidualCount [] = zero
rightResidualCount (rightResidual ∷ rest) = suc (rightResidualCount rest)
rightResidualCount (_ ∷ rest) = rightResidualCount rest

mlpStructure = Describe.describeNetwork Builder.mlp
encoderStructure = Describe.describeNetwork Builder.encoderBlock
independentTransformerStructure =
  Describe.describeNetwork Builder.twoIndependentBlocks
sharedTransformerStructure =
  Describe.describeNetwork Builder.twoSharedBlocks
independentSequenceStructure =
  Describe.describeNetwork threeIndependentLayers
sharedSequenceStructure = Describe.describeNetwork threeSharedLayers

mlp-forward-structure-agrees :
  projectNodes (forwardNodes mlpStructure) ≡
  ExistingSymbolic.nodes (Existing.interpretNetwork Builder.mlp)
mlp-forward-structure-agrees = refl

sequence-forward-structure-agrees :
  projectNodes (forwardNodes independentSequenceStructure) ≡
  ExistingSymbolic.nodes
    (Existing.interpretNetwork threeIndependentLayers)
sequence-forward-structure-agrees = refl

transformer-forward-structure-agrees :
  projectNodes (forwardNodes encoderStructure) ≡
  ExistingSymbolic.nodes
    (Existing.interpretNetwork Builder.encoderBlock)
transformer-forward-structure-agrees = refl

independent-stack-forward-structure-agrees :
  projectNodes (forwardNodes independentTransformerStructure) ≡
  ExistingSymbolic.nodes
    (Existing.interpretNetwork Builder.twoIndependentBlocks)
independent-stack-forward-structure-agrees = refl

shared-stack-forward-structure-agrees :
  projectNodes (forwardNodes sharedTransformerStructure) ≡
  ExistingSymbolic.nodes
    (Existing.interpretNetwork Builder.twoSharedBlocks)
shared-stack-forward-structure-agrees = refl

mlp-reverse-primitive-order :
  projectNodes (reverseNodes mlpStructure) ≡
  ExistingSymbolic.softmaxNode 1 ∷
  ExistingSymbolic.denseNode 3 1 ∷
  ExistingSymbolic.reluNode 3 ∷
  ExistingSymbolic.denseNode 2 3 ∷ []
mlp-reverse-primitive-order = refl

transformer-reverse-order :
  projectNodes (reverseNodes encoderStructure) ≡
  ExistingSymbolic.addTokensNode 4 8 ∷
  ExistingSymbolic.feedForwardNode 4 8 16 ∷
  ExistingSymbolic.layerNormNode 4 8 ∷
  ExistingSymbolic.copyDataNode ∷
  ExistingSymbolic.addTokensNode 4 8 ∷
  ExistingSymbolic.attentionNode 4 8 2 ∷
  ExistingSymbolic.layerNormNode 4 8 ∷
  ExistingSymbolic.copyDataNode ∷ []
transformer-reverse-order = refl

transformer-residual-aggregation-points :
  copyCount (reverseNodes encoderStructure) ≡ 2
transformer-residual-aggregation-points = refl

transformer-left-residual-paths :
  leftResidualCount (proj₂ (propagateArchitecture encoderLearner
    (4 ∷ᶜ 3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 1
    (primitiveReverse (ExistingSymbolic.addTokensNode 4 8) ∷ []))) ≡ 3
transformer-left-residual-paths = refl

transformer-right-residual-paths :
  rightResidualCount (proj₂ (propagateArchitecture encoderLearner
    (4 ∷ᶜ 3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 1
    (primitiveReverse (ExistingSymbolic.addTokensNode 4 8) ∷ []))) ≡ 3
transformer-right-residual-paths = refl

independent-stack-residual-aggregation-points :
  copyCount (reverseNodes independentTransformerStructure) ≡ 4
independent-stack-residual-aggregation-points = refl

shared-stack-residual-aggregation-points :
  copyCount (reverseNodes sharedTransformerStructure) ≡ 4
shared-stack-residual-aggregation-points = refl

------------------------------------------------------------------------
-- Shared Transformer occurrences aggregate into four external destinations.

independent-transformer-destinations :
  parameterDestinations (binding Builder.twoIndependentBlocks) ≡
  just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷
  just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ []
independent-transformer-destinations = refl

shared-transformer-destinations :
  parameterDestinations (binding Builder.twoSharedBlocks) ≡
  just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷
  just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ []
shared-transformer-destinations = refl

shared-transformer-aggregation-destinations :
  parameterAggregationSites (binding Builder.twoSharedBlocks) ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ []
shared-transformer-aggregation-destinations = refl

shared-transformer-eight-occurrences :
  ExistingSymbolic.rawParameterOccurrenceCount
    (Existing.interpretNetwork Builder.twoSharedBlocks) ≡ 8
shared-transformer-eight-occurrences = refl

shared-transformer-four-external-parameters :
  ExistingSymbolic.externalParameterCount
    (Existing.interpretNetwork Builder.twoSharedBlocks) ≡ 4
shared-transformer-four-external-parameters = refl

-- Actual abstract propagation witnesses that each external parameter receives
-- one ordered signal from each of its two occurrences.
shared-transformer-parameter-signals :
  proj₁ (propagateArchitecture sharedTransformerLearner
    (4 ∷ᶜ 3 ∷ᶜ 2 ∷ᶜ 1 ∷ᶜ []ᶜ) 1
    (primitiveReverse (ExistingSymbolic.addTokensNode 4 8) ∷ [])) ≡
  ( (parameterReverse
        (ExistingSymbolic.feedForwardNode 4 8 16) ∷
      parameterReverse
        (ExistingSymbolic.feedForwardNode 4 8 16) ∷ []) ∷ᶜ
    (parameterReverse (ExistingSymbolic.layerNormNode 4 8) ∷
      parameterReverse (ExistingSymbolic.layerNormNode 4 8) ∷ []) ∷ᶜ
    (parameterReverse (ExistingSymbolic.attentionNode 4 8 2) ∷
      parameterReverse (ExistingSymbolic.attentionNode 4 8 2) ∷ []) ∷ᶜ
    (parameterReverse (ExistingSymbolic.layerNormNode 4 8) ∷
      parameterReverse (ExistingSymbolic.layerNormNode 4 8) ∷ []) ∷ᶜ
    []ᶜ )
shared-transformer-parameter-signals = refl
