{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ArchitectureLanguage where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Architecture.Model
import ParaForge.Architecture.Instance.Sets as Sets
import ParaForge.Architecture.Instance.Symbolic as Symbolic

-- The examples are tagless-final: each architecture is defined once against
-- Model and receives executable and symbolic interpretations without first
-- committing ParaForge to an initial AST.
module ArchitectureExamples (M : Model) where
  open Model M

  private
    variable
      Γ : ParamCtx

  mlpInputWidth mlpHiddenWidth mlpOutputWidth : ℕ
  mlpInputWidth = 2
  mlpHiddenWidth = 3
  mlpOutputWidth = 1

  mlpFeature : Architecture
    (denseP mlpInputWidth mlpHiddenWidth ∷ [])
    (vector mlpInputWidth)
    (vector mlpHiddenWidth)
  mlpFeature = sequential
    (interpretPrimitive (dense mlpInputWidth mlpHiddenWidth))
    (interpretPrimitive (relu mlpHiddenWidth))

  mlpOutput : Architecture
    (denseP mlpHiddenWidth mlpOutputWidth ∷ [])
    (vector mlpHiddenWidth)
    (vector mlpOutputWidth)
  mlpOutput = sequential
    (interpretPrimitive (dense mlpHiddenWidth mlpOutputWidth))
    (interpretPrimitive (softmax mlpOutputWidth))

  mlp : Architecture
    (denseP mlpHiddenWidth mlpOutputWidth ∷
      denseP mlpInputWidth mlpHiddenWidth ∷ [])
    (vector mlpInputWidth)
    (vector mlpOutputWidth)
  mlp = sequential mlpFeature mlpOutput

  sequenceLength modelWidth headCount hiddenWidth : ℕ
  sequenceLength = 4
  modelWidth = 8
  headCount = 2
  hiddenWidth = 16

  TokenInterface : Interface
  TokenInterface = tokens sequenceLength modelWidth

  residual :
    Architecture Γ TokenInterface TokenInterface →
    Architecture Γ TokenInterface TokenInterface
  residual branch = restrict rightUnitWire
    (sequential
      (dataWire copyData)
      (sequential
        (parallel branch identity)
        (interpretPrimitive (addTokens sequenceLength modelWidth))))

  attentionBranch : Architecture
    (attentionP headCount modelWidth ∷
      layerNormP modelWidth ∷ [])
    TokenInterface TokenInterface
  attentionBranch = sequential
    (interpretPrimitive (layerNorm sequenceLength modelWidth))
    (interpretPrimitive
      (selfAttention sequenceLength modelWidth headCount))

  feedForwardBranch : Architecture
    (feedForwardP modelWidth hiddenWidth ∷
      layerNormP modelWidth ∷ [])
    TokenInterface TokenInterface
  feedForwardBranch = sequential
    (interpretPrimitive (layerNorm sequenceLength modelWidth))
    (interpretPrimitive
      (feedForward sequenceLength modelWidth hiddenWidth))

  BlockParameters : ParamCtx
  BlockParameters =
    feedForwardP modelWidth hiddenWidth ∷
    layerNormP modelWidth ∷
    attentionP headCount modelWidth ∷
    layerNormP modelWidth ∷ []

  encoderBlock : Architecture
    BlockParameters TokenInterface TokenInterface
  encoderBlock = sequential
    (residual attentionBranch)
    (residual feedForwardBranch)

  twoIndependentBlocks : Architecture
    (BlockParameters ++ BlockParameters)
    TokenInterface TokenInterface
  twoIndependentBlocks = sequential encoderBlock encoderBlock

  twoSharedBlocks : Architecture
    BlockParameters TokenInterface TokenInterface
  twoSharedBlocks =
    restrict duplicateWire twoIndependentBlocks

module Executable = ArchitectureExamples Sets.SetsModel
module Structure = ArchitectureExamples Symbolic.SymbolicModel

-- Later-layer parameters occur first. With output weight 5, input weight 4,
-- and input 3, the lightweight Sets semantics computes 5 + (4 + 3) = 12.
mlp-parameter-order-executes :
  Executable.mlp (5 ∷ₑ 4 ∷ₑ ε) 3 ≡ 12
mlp-parameter-order-executes = refl

-- The pre-norm block computes both residual branches. The parameter order is
-- feed-forward, second norm, attention, first norm.
transformer-block-executes :
  Executable.encoderBlock
    (4 ∷ₑ 3 ∷ₑ 2 ∷ₑ 1 ∷ₑ ε) 1 ≡ 17
transformer-block-executes = refl

independent-transformer-blocks-execute :
  Executable.twoIndependentBlocks
    (4 ∷ₑ 3 ∷ₑ 2 ∷ₑ 1 ∷ₑ
     4 ∷ₑ 3 ∷ₑ 2 ∷ₑ 1 ∷ₑ ε) 1 ≡ 81
independent-transformer-blocks-execute = refl

-- The same four external values are selected twice by duplicateWire.
shared-transformer-blocks-execute :
  Executable.twoSharedBlocks
    (4 ∷ₑ 3 ∷ₑ 2 ∷ₑ 1 ∷ₑ ε) 1 ≡ 81
shared-transformer-blocks-execute = refl

mlp-symbolic-external-parameters :
  Symbolic.externalParameterCount Structure.mlp ≡ 2
mlp-symbolic-external-parameters = refl

mlp-symbolic-raw-occurrences :
  Symbolic.rawParameterOccurrenceCount Structure.mlp ≡ 2
mlp-symbolic-raw-occurrences = refl

mlp-symbolic-sharing :
  Symbolic.sharingClasses Structure.mlp ≡ 0 ∷ 1 ∷ []
mlp-symbolic-sharing = refl

transformer-symbolic-nodes :
  Symbolic.nodes Structure.encoderBlock ≡
    Symbolic.copyDataNode ∷
    Symbolic.layerNormNode 4 8 ∷
    Symbolic.attentionNode 4 8 2 ∷
    Symbolic.addTokensNode 4 8 ∷
    Symbolic.copyDataNode ∷
    Symbolic.layerNormNode 4 8 ∷
    Symbolic.feedForwardNode 4 8 16 ∷
    Symbolic.addTokensNode 4 8 ∷ []
transformer-symbolic-nodes = refl

transformer-symbolic-depth :
  Symbolic.depth Structure.encoderBlock ≡ 8
transformer-symbolic-depth = refl

independent-transformer-external-parameters :
  Symbolic.externalParameterCount Structure.twoIndependentBlocks ≡ 8
independent-transformer-external-parameters = refl

independent-transformer-raw-occurrences :
  Symbolic.rawParameterOccurrenceCount Structure.twoIndependentBlocks ≡ 8
independent-transformer-raw-occurrences = refl

shared-transformer-external-parameters :
  Symbolic.externalParameterCount Structure.twoSharedBlocks ≡ 4
shared-transformer-external-parameters = refl

shared-transformer-raw-occurrences :
  Symbolic.rawParameterOccurrenceCount Structure.twoSharedBlocks ≡ 8
shared-transformer-raw-occurrences = refl

shared-transformer-classes :
  Symbolic.sharingClasses Structure.twoSharedBlocks ≡
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
shared-transformer-classes = refl
