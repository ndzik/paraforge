{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Tensor.Signature where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _*_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Tensor.Shape public

-- Parameter codes describe trainable values but contain no numerical arrays.
-- A linear parameter contains a pointwise weight matrix and bias. A
-- convolution parameter contains one same-padded stride-one kernel and bias.
data TensorParameter : Set where
  linearP : (inputFeatures outputFeatures : ℕ) → TensorParameter
  convolutionP :
    (kernelHeight kernelWidth inputChannels outputChannels : ℕ) →
    TensorParameter

TensorContext : Set
TensorContext = List TensorParameter

-- Activations form a closed backend-neutral vocabulary. Their numerical
-- interpretation belongs to an external runtime.
data Activation : Set where
  relu : Activation

-- Fixed kernels are architecture constants, not external trainable parameters.
-- ncaPerception denotes the standard channel-wise identity/Sobel-x/Sobel-y
-- bank. It maps C state channels to 3 * C perception channels.
data FixedKernel :
  (kernelHeight kernelWidth inputChannels outputChannels : ℕ) → Set where
  ncaPerception : (channels : ℕ) →
    FixedKernel 3 3 channels (3 * channels)

private
  variable
    height width channels : ℕ

-- Every primitive has one closed, shape-indexed meaning. Convolutions use
-- zero padding and unit stride, so their spatial dimensions are preserved.
data TensorPrimitive :
  TensorContext → Shape → Shape → Set where

  linear : ∀ height width inputFeatures outputFeatures →
    TensorPrimitive
      (linearP inputFeatures outputFeatures ∷ [])
      (grid height width inputFeatures)
      (grid height width outputFeatures)

  convolution :
    ∀ height width kernelHeight kernelWidth inputChannels outputChannels →
    TensorPrimitive
      (convolutionP kernelHeight kernelWidth
        inputChannels outputChannels ∷ [])
      (grid height width inputChannels)
      (grid height width outputChannels)

  fixedConvolution :
    ∀ height width {kernelHeight kernelWidth inputChannels outputChannels} →
    FixedKernel kernelHeight kernelWidth inputChannels outputChannels →
    TensorPrimitive []
      (grid height width inputChannels)
      (grid height width outputChannels)

  activate : ∀ height width channels → Activation →
    TensorPrimitive []
      (grid height width channels)
      (grid height width channels)

  add : ∀ height width channels →
    TensorPrimitive []
      (grid height width channels ×ˢ grid height width channels)
      (grid height width channels)

-- Phase 35 admits no arbitrary generated parameter transformations. Cartesian
-- selection still provides explicit identity, deletion, and sharing.
data NoTensorReparameterization
  (external occurrences : TensorContext) : Set where

TensorSignature : Signature 0ℓ 0ℓ 0ℓ
TensorSignature = record
  { InterfaceCode = Shape
  ; ParameterCode = TensorParameter
  ; PrimitiveCode = TensorPrimitive
  ; ReparameterizationCode = NoTensorReparameterization
  ; Shareable = λ _ → ⊤
  }

TensorDataflow : DataflowSignature TensorSignature
TensorDataflow = record
  { unitInterface = unit
  ; tensorInterface = _×ˢ_
  }
