{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Export.IR where

open import Data.Nat.Base using (ℕ)

open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Tensor.Shape
open import ParaForge.Architecture.Tensor.Signature

private
  variable
    A B C D : Shape
    Π : TensorContext
    height width channels : ℕ

-- Bound primitives refer directly to the document's global external parameter
-- context. The source architecture's occurrence context and ParamWire have
-- already been resolved before a value of this type is constructed.
data BoundPrimitive
  (Π : TensorContext) : Shape → Shape → Set where

  linear : ∀ height width inputFeatures outputFeatures →
    Slot TensorSignature (linearP inputFeatures outputFeatures) Π →
    BoundPrimitive Π
      (grid height width inputFeatures)
      (grid height width outputFeatures)

  convolution :
    ∀ height width kernelHeight kernelWidth inputChannels outputChannels →
    Slot TensorSignature
      (convolutionP kernelHeight kernelWidth
        inputChannels outputChannels) Π →
    BoundPrimitive Π
      (grid height width inputChannels)
      (grid height width outputChannels)

  fixedConvolution :
    ∀ height width {kernelHeight kernelWidth inputChannels outputChannels} →
    FixedKernel kernelHeight kernelWidth inputChannels outputChannels →
    BoundPrimitive Π
      (grid height width inputChannels)
      (grid height width outputChannels)

  activate : ∀ height width channels → Activation →
    BoundPrimitive Π
      (grid height width channels)
      (grid height width channels)

  add : ∀ height width channels →
    BoundPrimitive Π
      (grid height width channels ×ˢ grid height width channels)
      (grid height width channels)

-- Operation is a closed, typed compilation target. Unlike CartesianArch, all
-- children share one global external parameter context Π.
data Operation
  (Π : TensorContext) : Shape → Shape → Set where

  identity : Operation Π A A

  primitiveOp : BoundPrimitive Π A B → Operation Π A B

  sequential :
    Operation Π A B → Operation Π B C → Operation Π A C

  parallel :
    Operation Π A B → Operation Π C D →
    Operation Π (A ×ˢ C) (B ×ˢ D)

  dataWire : DataWire TensorDataflow A B → Operation Π A B

  repeat : (count : ℕ) → Operation Π A A → Operation Π A A

-- Version is part of the typed target rather than an unvalidated JSON number.
data Version : Set where
  v1 : Version

record Document
  (Π : TensorContext) (A B : Shape) : Set where
  constructor document
  field
    version : Version
    operation : Operation Π A B

open Document public
