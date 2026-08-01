{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ArchitectureBuilder where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import ParaForge.Architecture.Model as Neural
open import ParaForge.Architecture.Core using (Occurrences)
open import ParaForge.Architecture.Interpretation
open import ParaForge.Architecture.Builder.Neural
import ParaForge.Architecture.Instance.Sets as Sets
import ParaForge.Architecture.Instance.Symbolic as Symbolic

-- The MLP now reads as an ordinary Agda-embedded composition. Its intrinsic
-- type still records the later-before-earlier parameter context.
mlp : NeuralModule
  (Neural.denseP 3 1 ∷ Neural.denseP 2 3 ∷ [])
  (Neural.vector 2)
  (Neural.vector 1)
mlp =
  dense 2 3 >>>
  relu 3 >>>
  dense 3 1 >>>
  softmax 1

sequenceLength modelWidth headCount hiddenWidth : ℕ
sequenceLength = 4
modelWidth = 8
headCount = 2
hiddenWidth = 16

BlockParameters : Neural.ParamCtx
BlockParameters =
  Neural.feedForwardP modelWidth hiddenWidth ∷
  Neural.layerNormP modelWidth ∷
  Neural.attentionP headCount modelWidth ∷
  Neural.layerNormP modelWidth ∷ []

-- Agda names provide the surface parameter declarations. Their values are
-- intrinsically typed references into BlockParameters.
ffnParameter : ParameterRef
  (Neural.feedForwardP modelWidth hiddenWidth) BlockParameters
ffnParameter = firstParameter

secondNormParameter : ParameterRef
  (Neural.layerNormP modelWidth) BlockParameters
secondNormParameter = nextParameter firstParameter

attentionParameter : ParameterRef
  (Neural.attentionP headCount modelWidth) BlockParameters
attentionParameter =
  nextParameter (nextParameter firstParameter)

firstNormParameter : ParameterRef
  (Neural.layerNormP modelWidth) BlockParameters
firstNormParameter =
  nextParameter (nextParameter (nextParameter firstParameter))

TokenInterface : Neural.Interface
TokenInterface = Neural.tokens sequenceLength modelWidth

attentionBranch : NeuralModule
  BlockParameters TokenInterface TokenInterface
attentionBranch =
  layerNormUsing {sequenceLength = sequenceLength} firstNormParameter >>>ˢ
  selfAttentionUsing {sequenceLength = sequenceLength} attentionParameter

feedForwardBranch : NeuralModule
  BlockParameters TokenInterface TokenInterface
feedForwardBranch =
  layerNormUsing {sequenceLength = sequenceLength} secondNormParameter >>>ˢ
  feedForwardUsing {sequenceLength = sequenceLength} ffnParameter

-- These names are ordinary Agda bindings for intermediate architecture
-- modules. residualTokens elaborates activation fan-out and recombination.
afterAttention : NeuralModule
  BlockParameters TokenInterface TokenInterface
afterAttention = residualTokens sequenceLength modelWidth attentionBranch

afterFeedForward : NeuralModule
  BlockParameters TokenInterface TokenInterface
afterFeedForward = residualTokens sequenceLength modelWidth feedForwardBranch

encoderBlock : NeuralModule
  BlockParameters TokenInterface TokenInterface
encoderBlock = afterAttention >>>ˢ afterFeedForward

twoIndependentBlocks : NeuralModule
  (BlockParameters ++ BlockParameters)
  TokenInterface TokenInterface
twoIndependentBlocks =
  repeatIndependent 2 encoderBlock

twoSharedBlocks : NeuralModule
  BlockParameters TokenInterface TokenInterface
twoSharedBlocks = repeatSharedNeural 2 encoderBlock

-- Reusing the same named declaration twice elaborates to one external
-- parameter controlling two primitive occurrences.
SharedDenseParameters : Neural.ParamCtx
SharedDenseParameters = Neural.denseP 3 3 ∷ []

sharedDenseParameter : ParameterRef
  (Neural.denseP 3 3) SharedDenseParameters
sharedDenseParameter = firstParameter

sharedDenseLayer : NeuralModule
  SharedDenseParameters (Neural.vector 3) (Neural.vector 3)
sharedDenseLayer = denseUsing sharedDenseParameter

twoSharedDenseLayers : NeuralModule
  SharedDenseParameters (Neural.vector 3) (Neural.vector 3)
twoSharedDenseLayers = sharedDenseLayer >>>ˢ sharedDenseLayer

module Execute = Interpret Sets.SetsModel
module Describe = Interpret Symbolic.SymbolicModel

mlp-builder-executes :
  Execute.interpretNetwork mlp
    (5 Neural.∷ₑ 4 Neural.∷ₑ Neural.ε) 3 ≡ 12
mlp-builder-executes = refl

transformer-builder-executes :
  Execute.interpretNetwork encoderBlock
    (4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 1
    ≡ 17
transformer-builder-executes = refl

independent-repetition-executes :
  Execute.interpretNetwork twoIndependentBlocks
    (4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ
     4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 1
    ≡ 81
independent-repetition-executes = refl

shared-repetition-executes :
  Execute.interpretNetwork twoSharedBlocks
    (4 Neural.∷ₑ 3 Neural.∷ₑ 2 Neural.∷ₑ 1 Neural.∷ₑ Neural.ε) 1
    ≡ 81
shared-repetition-executes = refl

lexical-sharing-executes :
  Execute.interpretNetwork twoSharedDenseLayers
    (2 Neural.∷ₑ Neural.ε) 1 ≡ 5
lexical-sharing-executes = refl

transformer-builder-raw-occurrences :
  Symbolic.rawParameterOccurrenceCount
    (Describe.interpretNetwork encoderBlock) ≡ 4
transformer-builder-raw-occurrences = refl

transformer-builder-sharing-classes :
  Symbolic.sharingClasses
    (Describe.interpretNetwork encoderBlock) ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ []
transformer-builder-sharing-classes = refl

independent-builder-external-parameters :
  Symbolic.externalParameterCount
    (Describe.interpretNetwork twoIndependentBlocks) ≡ 8
independent-builder-external-parameters = refl

shared-builder-external-parameters :
  Symbolic.externalParameterCount
    (Describe.interpretNetwork twoSharedBlocks) ≡ 4
shared-builder-external-parameters = refl

shared-builder-raw-occurrences :
  Symbolic.rawParameterOccurrenceCount
    (Describe.interpretNetwork twoSharedBlocks) ≡ 8
shared-builder-raw-occurrences = refl

shared-builder-classes :
  Symbolic.sharingClasses
    (Describe.interpretNetwork twoSharedBlocks) ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
shared-builder-classes = refl

lexical-sharing-classes :
  Symbolic.sharingClasses
    (Describe.interpretNetwork twoSharedDenseLayers) ≡
  0 ∷ 0 ∷ []
lexical-sharing-classes = refl
