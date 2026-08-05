{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Export.Compile where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core
import ParaForge.Architecture.Builder as Generic
open import ParaForge.Architecture.Tensor.Shape
open import ParaForge.Architecture.Tensor.Signature
open import ParaForge.Architecture.Export.IR

module Build = Generic.Build TensorDataflow

private
  variable
    A B C D : Shape
    Γ Δ Θ : TensorContext

-- A selection is a typed environment of references into one global external
-- context. Splitting follows ParaForge's later-before-earlier list order.
splitSelection :
  (Δ : TensorContext) →
  Selection TensorSignature Θ (Δ ++ Γ) →
  Selection TensorSignature Θ Δ × Selection TensorSignature Θ Γ
splitSelection [] selection = select[] , selection
splitSelection (_ ∷ Δ) (select slot rest) with splitSelection Δ rest
... | left , right = select slot left , right

wireExternal :
  ParamWire TensorSignature Δ Γ → TensorContext
wireExternal {Δ = Δ} wire = Δ

-- Interpret a source parameter wire as transport of global typed references.
-- The tensor signature has no generated reparameterization constructors.
applyParamWire :
  ParamWire TensorSignature Δ Γ →
  Selection TensorSignature Θ Δ →
  Selection TensorSignature Θ Γ
applyParamWire identity references = references
applyParamWire (later ∘w earlier) references =
  applyParamWire later (applyParamWire earlier references)
applyParamWire (left ⊗w right) references
  with splitSelection (wireExternal left) references
... | leftReferences , rightReferences =
  appendSelection TensorSignature
    (applyParamWire left leftReferences)
    (applyParamWire right rightReferences)
applyParamWire (generated ()) references
applyParamWire (cartesian evidence selection) references =
  composeSelection TensorSignature references selection
applyParamWire rightUnit references =
  appendSelection TensorSignature references select[]

compilePrimitive :
  Selection TensorSignature Θ Γ →
  TensorPrimitive Γ A B →
  BoundPrimitive Θ A B
compilePrimitive (select parameter select[])
  (TensorPrimitive.linear height width inputFeatures outputFeatures) =
  BoundPrimitive.linear height width inputFeatures outputFeatures parameter
compilePrimitive (select parameter select[])
  (TensorPrimitive.convolution height width
    kernelHeight kernelWidth inputChannels outputChannels) =
  BoundPrimitive.convolution height width
    kernelHeight kernelWidth inputChannels outputChannels parameter
compilePrimitive select[]
  (TensorPrimitive.fixedConvolution height width kernel) =
  BoundPrimitive.fixedConvolution height width kernel
compilePrimitive select[]
  (TensorPrimitive.activate height width channels activation) =
  BoundPrimitive.activate height width channels activation
compilePrimitive select[]
  (TensorPrimitive.add height width channels) =
  BoundPrimitive.add height width channels

coreContext : CoreArch TensorSignature Γ A B → TensorContext
coreContext {Γ = Γ} architecture = Γ

cartesianContext :
  CartesianArch TensorDataflow Γ A B → TensorContext
cartesianContext {Γ = Γ} architecture = Γ

compileCore :
  Selection TensorSignature Θ Γ →
  CoreArch TensorSignature Γ A B →
  Operation Θ A B
compileCore references idA = identity
compileCore references (primA primitiveCode) =
  primitiveOp (compilePrimitive references primitiveCode)
compileCore references (first >>>A later)
  with splitSelection (coreContext later) references
... | laterReferences , firstReferences =
  sequential
    (compileCore firstReferences first)
    (compileCore laterReferences later)
compileCore references (restrictA wire architecture) =
  compileCore (applyParamWire wire references) architecture

compileCartesian :
  Selection TensorSignature Θ Γ →
  CartesianArch TensorDataflow Γ A B →
  Operation Θ A B
compileCartesian references (core architecture) =
  compileCore references architecture
compileCartesian references (first >>>C later)
  with splitSelection (cartesianContext later) references
... | laterReferences , firstReferences =
  sequential
    (compileCartesian firstReferences first)
    (compileCartesian laterReferences later)
compileCartesian references (left ***C right)
  with splitSelection (cartesianContext right) references
... | rightReferences , leftReferences =
  parallel
    (compileCartesian leftReferences left)
    (compileCartesian rightReferences right)
compileCartesian references (wireC wire) = dataWire wire
compileCartesian references (restrictC wire architecture) =
  compileCartesian (applyParamWire wire references) architecture

compileNetwork :
  Network TensorDataflow Γ A B → Document Γ A B
compileNetwork architecture = document v1
  (compileCartesian
    (applyParamWire (binding architecture)
      (idSelection TensorSignature))
    (body architecture))

-- Repetition remains derived in the source language. This explicit compilation
-- entry point retains its provenance in the target without guessing that an
-- expanded sequential tree was originally produced by repeatShared.
compileSharedRollout :
  (count : ℕ) →
  Network TensorDataflow Γ A A →
  Document (Build.sharedContext count Γ) A A
compileSharedRollout zero architecture = document v1 identity
compileSharedRollout (suc count) architecture = document v1
  (repeat (suc count) (operation (compileNetwork architecture)))
