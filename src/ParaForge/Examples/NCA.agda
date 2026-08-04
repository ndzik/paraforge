{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.NCA where

open import Data.List.Base using ([]; _∷_; _++_; length)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; _*_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core
import ParaForge.Architecture.Builder as Generic
open import ParaForge.Architecture.Tensor.Shape
open import ParaForge.Architecture.Tensor.Signature
open import ParaForge.Learning.Architecture.Symbolic

module Build = Generic.Build TensorDataflow
module Describe = DescribeArchitecture TensorDataflow

private
  variable
    A B C : Shape
    P : TensorParameter
    Γ Δ : TensorContext

TensorModule : TensorContext → Shape → Shape → Set
TensorModule = Build.Module

infixl 6 _>>>_

_>>>_ :
  TensorModule Γ A B → TensorModule Δ B C →
  TensorModule (Δ ++ Γ) A C
first >>> later = Build._>>>_ first later

parameterized :
  TensorPrimitive (P ∷ []) A B → TensorModule (P ∷ []) A B
parameterized {P = P} operation = network
  (P ∷ [])
  (primC TensorDataflow operation)
  identity

parameterFree : TensorPrimitive [] A B → TensorModule [] A B
parameterFree operation = network
  []
  (primC TensorDataflow operation)
  identity

allTensorShareable : AllShareable TensorSignature Γ
allTensorShareable {Γ = []} = shareable[]
allTensorShareable {Γ = _ ∷ Γ} =
  tt ∷ₛ allTensorShareable

-- A deliberately small deterministic NCA configuration. Numerical values,
-- initialization, and execution remain responsibilities of the future runtime.
gridHeight gridWidth stateChannels perceptionChannels hiddenChannels : ℕ
gridHeight = 16
gridWidth = 16
stateChannels = 4
perceptionChannels = 3 * stateChannels
hiddenChannels = 16

NcaState : Shape
NcaState = grid gridHeight gridWidth stateChannels

NcaParameters : TensorContext
NcaParameters =
  linearP hiddenChannels stateChannels ∷
  linearP perceptionChannels hiddenChannels ∷ []

perceive : TensorModule [] NcaState
  (grid gridHeight gridWidth perceptionChannels)
perceive = parameterFree
  (fixedConvolution gridHeight gridWidth
    (ncaPerception stateChannels))

hiddenUpdate : TensorModule
  (linearP perceptionChannels hiddenChannels ∷ [])
  (grid gridHeight gridWidth perceptionChannels)
  (grid gridHeight gridWidth hiddenChannels)
hiddenUpdate = parameterized
  (linear gridHeight gridWidth perceptionChannels hiddenChannels)

activateUpdate : TensorModule []
  (grid gridHeight gridWidth hiddenChannels)
  (grid gridHeight gridWidth hiddenChannels)
activateUpdate = parameterFree
  (activate gridHeight gridWidth hiddenChannels relu)

stateUpdate : TensorModule
  (linearP hiddenChannels stateChannels ∷ [])
  (grid gridHeight gridWidth hiddenChannels)
  NcaState
stateUpdate = parameterized
  (linear gridHeight gridWidth hiddenChannels stateChannels)

-- The later-before-earlier convention puts the state projection before the
-- hidden projection in NcaParameters.
ncaDelta : TensorModule NcaParameters NcaState NcaState
ncaDelta =
  perceive >>>
  hiddenUpdate >>>
  activateUpdate >>>
  stateUpdate

addState : CartesianArch TensorDataflow []
  (NcaState ×ˢ NcaState) NcaState
addState = primC TensorDataflow
  (add gridHeight gridWidth stateChannels)

-- Residual update is derived from copy, parallel composition, and addition.
-- No dedicated NCA or residual constructor is added to the architecture core.
ncaStep : TensorModule NcaParameters NcaState NcaState
ncaStep = Build.residualWith addState ncaDelta

rolloutLength : ℕ
rolloutLength = 4

-- repeatShared accepts only endomorphisms and retains one external parameter
-- context. All four steps therefore reference the same two update parameters.
ncaRollout : TensorModule NcaParameters NcaState NcaState
ncaRollout = Build.repeatShared rolloutLength
  allTensorShareable ncaStep

perception-is-fixed : Occurrences perceive ≡ []
perception-is-fixed = refl

step-has-two-parameter-occurrences :
  length (Occurrences ncaStep) ≡ 2
step-has-two-parameter-occurrences = refl

rollout-has-two-external-parameters :
  length NcaParameters ≡ 2
rollout-has-two-external-parameters = refl

rollout-has-eight-parameter-occurrences :
  length (Occurrences ncaRollout) ≡ 8
rollout-has-eight-parameter-occurrences = refl

rollout-sharing-destinations :
  parameterDestinations (binding ncaRollout) ≡
  just 0 ∷ just 1 ∷
  just 0 ∷ just 1 ∷
  just 0 ∷ just 1 ∷
  just 0 ∷ just 1 ∷ []
rollout-sharing-destinations = refl

rollout-aggregation-sites :
  parameterAggregationSites (binding ncaRollout) ≡
  0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []
rollout-aggregation-sites = refl

-- This definitional check keeps the residual convention observable: same-input
-- branching is copyData followed by split-input parallelism and explicit add.
step-is-derived-residual :
  body ncaStep ≡
  restrictC rightUnit
    (wireC copyData >>>C
      ((body ncaDelta ***C idC TensorDataflow) >>>C addState))
step-is-derived-residual = refl
