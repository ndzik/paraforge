{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Builder.Neural where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Polymorphic.Base using (tt)

import ParaForge.Architecture.Model as Neural
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core
open import ParaForge.Architecture.Interpretation
import ParaForge.Architecture.Builder as Generic

private
  variable
    A B C : Neural.Interface
    P Q : Neural.Parameter
    Π QCtx : Neural.ParamCtx
    inputWidth outputWidth : ℕ
    sequenceLength modelWidth heads hiddenWidth : ℕ

ParameterRef : Neural.Parameter → Neural.ParamCtx → Set
ParameterRef = Slot NeuralSignature

firstParameter : ParameterRef P (P ∷ Π)
firstParameter = here

nextParameter : ParameterRef P Π → ParameterRef P (Q ∷ Π)
nextParameter = there

-- The validated neural signature declares every parameter code shareable.
-- Generic signatures need not provide this function.
allNeuralShareable : AllShareable NeuralSignature Π
allNeuralShareable {Π = []} = shareable[]
allNeuralShareable {Π = _ ∷ Π} =
  tt ∷ₛ allNeuralShareable

NeuralModule : Neural.ParamCtx → Neural.Interface → Neural.Interface → Set
NeuralModule = Generic.Module NeuralDataflow

infixl 6 _>>>_

_>>>_ :
  NeuralModule Π A B → NeuralModule QCtx B C →
  NeuralModule (QCtx ++ Π) A C
first >>> later = Generic._>>>_ NeuralDataflow first later

parameterized :
  ParameterRef P Π →
  Neural.Primitive (P ∷ []) A B →
  NeuralModule Π A B
parameterized {P = P} reference operation = network
  (P ∷ [])
  (primC NeuralDataflow operation)
  (cartesian allNeuralShareable
    (select reference select[]))

parameterFree :
  Neural.Primitive [] A B → NeuralModule [] A B
parameterFree operation = network
  []
  (primC NeuralDataflow operation)
  identity

-- A layer owning its own parameter declaration.
dense : ∀ inputWidth outputWidth →
  NeuralModule
    (Neural.denseP inputWidth outputWidth ∷ [])
    (Neural.vector inputWidth)
    (Neural.vector outputWidth)
dense inputWidth outputWidth = parameterized firstParameter
  (Neural.dense inputWidth outputWidth)

-- A layer referring to a named declaration in a larger lexical scope.
denseUsing :
  ParameterRef (Neural.denseP inputWidth outputWidth) Π →
  NeuralModule Π
    (Neural.vector inputWidth)
    (Neural.vector outputWidth)
denseUsing reference = parameterized reference
  (Neural.dense _ _)

relu : ∀ width → NeuralModule []
  (Neural.vector width) (Neural.vector width)
relu width = parameterFree (Neural.relu width)

softmax : ∀ width → NeuralModule []
  (Neural.vector width) (Neural.vector width)
softmax width = parameterFree (Neural.softmax width)

layerNormUsing :
  ParameterRef (Neural.layerNormP modelWidth) Π →
  NeuralModule Π
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth)
layerNormUsing {modelWidth = modelWidth}
  {sequenceLength = sequenceLength} reference =
  parameterized reference
    (Neural.layerNorm sequenceLength modelWidth)

selfAttentionUsing :
  ParameterRef (Neural.attentionP heads modelWidth) Π →
  NeuralModule Π
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth)
selfAttentionUsing {heads = heads} {modelWidth = modelWidth}
  {sequenceLength = sequenceLength} reference =
  parameterized reference
    (Neural.selfAttention sequenceLength modelWidth heads)

feedForwardUsing :
  ParameterRef (Neural.feedForwardP modelWidth hiddenWidth) Π →
  NeuralModule Π
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth)
feedForwardUsing {modelWidth = modelWidth} {hiddenWidth = hiddenWidth}
  {sequenceLength = sequenceLength} reference =
  parameterized reference
    (Neural.feedForward sequenceLength modelWidth hiddenWidth)

infixl 6 _>>>ˢ_

-- Compose within one named parameter scope. Repeated references elaborate to
-- capability-checked copying in ParamWire.
_>>>ˢ_ :
  NeuralModule Π A B → NeuralModule Π B C → NeuralModule Π A C
first >>>ˢ later =
  Generic.composeShared NeuralDataflow allNeuralShareable first later

residualTokens :
  ∀ sequenceLength modelWidth →
  NeuralModule Π
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth) →
  NeuralModule Π
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth)
residualTokens sequenceLength modelWidth =
  Generic.residualWith NeuralDataflow
    (primC NeuralDataflow
      (Neural.addTokens sequenceLength modelWidth))

repeatIndependent :
  (count : ℕ) → NeuralModule Π A A →
  NeuralModule (Generic.repeatContext NeuralDataflow count Π) A A
repeatIndependent count architecture =
  Generic.repeatIndependent NeuralDataflow count architecture

repeatSharedNeural :
  (count : ℕ) → NeuralModule Π A A →
  NeuralModule (Generic.sharedContext NeuralDataflow count Π) A A
repeatSharedNeural count architecture =
  Generic.repeatShared NeuralDataflow count
    allNeuralShareable architecture
