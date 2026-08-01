{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ArchitectureCore where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import ParaForge.Architecture.Model as Final
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core
open import ParaForge.Architecture.Transformation
open import ParaForge.Architecture.Interpretation
import ParaForge.Architecture.Instance.Sets as Sets
import ParaForge.Architecture.Instance.Symbolic as Symbolic
import ParaForge.Examples.ArchitectureLanguage as Phase27
import ParaForge.Para.Set.Reparameterization as ConcreteCells

private
  variable
    Γ : Final.ParamCtx

mlpInputWidth mlpHiddenWidth mlpOutputWidth : ℕ
mlpInputWidth = 2
mlpHiddenWidth = 3
mlpOutputWidth = 1

mlpCore : CoreArch NeuralSignature
  (Final.denseP mlpHiddenWidth mlpOutputWidth ∷
    Final.denseP mlpInputWidth mlpHiddenWidth ∷ [])
  (Final.vector mlpInputWidth)
  (Final.vector mlpOutputWidth)
mlpCore =
  (primA (Final.dense mlpInputWidth mlpHiddenWidth) >>>A
    primA (Final.relu mlpHiddenWidth)) >>>A
  (primA (Final.dense mlpHiddenWidth mlpOutputWidth) >>>A
    primA (Final.softmax mlpOutputWidth))

sequenceLength modelWidth headCount hiddenWidth : ℕ
sequenceLength = 4
modelWidth = 8
headCount = 2
hiddenWidth = 16

TokenInterface : Final.Interface
TokenInterface = Final.tokens sequenceLength modelWidth

residualCore :
  CartesianArch NeuralDataflow Γ TokenInterface TokenInterface →
  CartesianArch NeuralDataflow Γ TokenInterface TokenInterface
residualCore branch = restrictC rightUnit
  (wireC copyData >>>C
    ((branch ***C idC NeuralDataflow) >>>C
      primC NeuralDataflow (Final.addTokens sequenceLength modelWidth)))

attentionBranchCore : CartesianArch NeuralDataflow
  (Final.attentionP headCount modelWidth ∷
    Final.layerNormP modelWidth ∷ [])
  TokenInterface TokenInterface
attentionBranchCore =
  primC NeuralDataflow (Final.layerNorm sequenceLength modelWidth) >>>C
  primC NeuralDataflow (Final.selfAttention sequenceLength modelWidth headCount)

feedForwardBranchCore : CartesianArch NeuralDataflow
  (Final.feedForwardP modelWidth hiddenWidth ∷
    Final.layerNormP modelWidth ∷ [])
  TokenInterface TokenInterface
feedForwardBranchCore =
  primC NeuralDataflow (Final.layerNorm sequenceLength modelWidth) >>>C
  primC NeuralDataflow (Final.feedForward sequenceLength modelWidth hiddenWidth)

BlockParameters : Final.ParamCtx
BlockParameters =
  Final.feedForwardP modelWidth hiddenWidth ∷
  Final.layerNormP modelWidth ∷
  Final.attentionP headCount modelWidth ∷
  Final.layerNormP modelWidth ∷ []

blockShareable : AllShareable NeuralSignature BlockParameters
blockShareable = tt ∷ₛ tt ∷ₛ tt ∷ₛ tt ∷ₛ shareable[]

encoderBlockCore : CartesianArch NeuralDataflow
  BlockParameters TokenInterface TokenInterface
encoderBlockCore =
  residualCore attentionBranchCore >>>C
  residualCore feedForwardBranchCore

twoIndependentBlocksCore : CartesianArch NeuralDataflow
  (BlockParameters ++ BlockParameters)
  TokenInterface TokenInterface
twoIndependentBlocksCore = encoderBlockCore >>>C encoderBlockCore

twoSharedBlocksCore : CartesianArch NeuralDataflow
  BlockParameters TokenInterface TokenInterface
twoSharedBlocksCore = restrictC
  (copyParameters NeuralSignature blockShareable)
  twoIndependentBlocksCore

sharedBlocksNetwork : Network NeuralDataflow
  BlockParameters TokenInterface TokenInterface
sharedBlocksNetwork = network
  (BlockParameters ++ BlockParameters)
  twoIndependentBlocksCore
  (copyParameters NeuralSignature blockShareable)

module Execute = Interpret Sets.SetsModel
module Describe = Interpret Symbolic.SymbolicModel

mlp-reifies-executable-semantics :
  Execute.interpretCore mlpCore
    (5 Final.∷ₑ 4 Final.∷ₑ Final.ε) 3 ≡
  Phase27.Executable.mlp
    (5 Final.∷ₑ 4 Final.∷ₑ Final.ε) 3
mlp-reifies-executable-semantics = refl

transformer-reifies-executable-semantics :
  Execute.interpretCartesian encoderBlockCore
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) 1 ≡
  Phase27.Executable.encoderBlock
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) 1
transformer-reifies-executable-semantics = refl

shared-repetition-reifies-executable-semantics :
  Execute.interpretCartesian twoSharedBlocksCore
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) 1 ≡ 81
shared-repetition-reifies-executable-semantics = refl

body-plus-binding-executes :
  Execute.interpretNetwork sharedBlocksNetwork
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) 1 ≡ 81
body-plus-binding-executes = refl

transformer-reifies-symbolic-nodes :
  Symbolic.nodes
    (Describe.interpretCartesian encoderBlockCore) ≡
  Symbolic.nodes Phase27.Structure.encoderBlock
transformer-reifies-symbolic-nodes = refl

shared-repetition-reifies-symbolic-classes :
  Symbolic.sharingClasses
    (Describe.interpretCartesian twoSharedBlocksCore) ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
shared-repetition-reifies-symbolic-classes = refl

body-plus-binding-symbolic-classes :
  Symbolic.sharingClasses
    (Describe.interpretNetwork sharedBlocksNetwork) ≡
  0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
body-plus-binding-symbolic-classes = refl

sharedArchitectureCell : ArchitectureCell NeuralDataflow
  twoIndependentBlocksCore twoSharedBlocksCore
sharedArchitectureCell = restrictionCell
  (copyParameters NeuralSignature blockShareable)

sharedAfterIdentity : ArchitectureCell NeuralDataflow
  twoIndependentBlocksCore twoSharedBlocksCore
sharedAfterIdentity = sharedArchitectureCell ∘vCell idCell

encoderHorizontalIdentity : ArchitectureCell NeuralDataflow
  encoderBlockCore encoderBlockCore
encoderHorizontalIdentity = idCell ∘hCell idCell

interpreted-horizontal-identity-map :
  ConcreteCells.mapParameters
    (InterpretSetsCells.interpretCell encoderHorizontalIdentity)
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) ≡
  4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε
interpreted-horizontal-identity-map = refl

interpreted-vertical-restriction-map :
  ConcreteCells.mapParameters
    (InterpretSetsCells.interpretCell sharedAfterIdentity)
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) ≡
  4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ
  4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε
interpreted-vertical-restriction-map = refl

-- Reified copy restriction still packages as the established concrete G.1
-- cell. Its backwards parameter map copies the four external values.
sharedCoreCell : ConcreteCells.Reparameterization
  (Sets.toPara {A = TokenInterface} {B = TokenInterface}
    (Execute.interpretCartesian twoIndependentBlocksCore))
  (Sets.toPara {A = TokenInterface} {B = TokenInterface}
    (Execute.interpretCartesian twoSharedBlocksCore))
sharedCoreCell = Sets.restrictionCell
  {A = TokenInterface} {B = TokenInterface}
  (eraseParamWire (copyParameters NeuralSignature blockShareable))
  (Execute.interpretCartesian twoIndependentBlocksCore)

shared-core-cell-copies-parameters :
  ConcreteCells.mapParameters sharedCoreCell
    (4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε) ≡
  4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ
  4 Final.∷ₑ 3 Final.∷ₑ 2 Final.∷ₑ 1 Final.∷ₑ Final.ε
shared-core-cell-copies-parameters = refl
