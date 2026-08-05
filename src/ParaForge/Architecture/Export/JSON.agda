{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Export.JSON where

import Data.List.Base as List
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Show as Nat
open import Data.Product.Base using (_×_; _,_)
import Data.String.Base as String
open import Data.String.Base using (String)

open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Tensor.Shape
open import ParaForge.Architecture.Tensor.Signature
open import ParaForge.Architecture.Export.IR

infixr 5 _++ₛ_

_++ₛ_ : String → String → String
_++ₛ_ = String._++_

-- A deliberately small pure JSON value language is sufficient for the closed
-- version-1 schema. String.show supplies quoting and escaping.
data JSON : Set where
  object : List (String × JSON) → JSON
  array : List JSON → JSON
  string : String → JSON
  natural : ℕ → JSON

mutual
  renderFields : List (String × JSON) → String
  renderFields [] = ""
  renderFields ((key , value) ∷ []) =
    String.show key ++ₛ ":" ++ₛ renderJSON value
  renderFields ((key , value) ∷ rest) =
    String.show key ++ₛ ":" ++ₛ renderJSON value ++ₛ
    "," ++ₛ renderFields rest

  renderValues : List JSON → String
  renderValues [] = ""
  renderValues (value ∷ []) = renderJSON value
  renderValues (value ∷ rest) =
    renderJSON value ++ₛ "," ++ₛ renderValues rest

  renderJSON : JSON → String
  renderJSON (object fields) = "{" ++ₛ renderFields fields ++ₛ "}"
  renderJSON (array values) = "[" ++ₛ renderValues values ++ₛ "]"
  renderJSON (string value) = String.show value
  renderJSON (natural value) = Nat.show value

shapeJSON : Shape → JSON
shapeJSON unit = object
  (("type" , string "unit") ∷ [])
shapeJSON scalar = object
  (("type" , string "scalar") ∷ [])
shapeJSON (vector features) = object
  ( ("type" , string "vector")
  ∷ ("features" , natural features)
  ∷ [])
shapeJSON (grid height width channels) = object
  ( ("type" , string "grid")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("channels" , natural channels)
  ∷ [])
shapeJSON (left ×ˢ right) = object
  ( ("type" , string "product")
  ∷ ("left" , shapeJSON left)
  ∷ ("right" , shapeJSON right)
  ∷ [])

parameterJSON : ℕ → TensorParameter → JSON
parameterJSON identifier (linearP inputFeatures outputFeatures) = object
  ( ("id" , natural identifier)
  ∷ ("kind" , string "linear")
  ∷ ("input_features" , natural inputFeatures)
  ∷ ("output_features" , natural outputFeatures)
  ∷ [])
parameterJSON identifier
  (convolutionP kernelHeight kernelWidth
    inputChannels outputChannels) = object
  ( ("id" , natural identifier)
  ∷ ("kind" , string "convolution")
  ∷ ("kernel_height" , natural kernelHeight)
  ∷ ("kernel_width" , natural kernelWidth)
  ∷ ("input_channels" , natural inputChannels)
  ∷ ("output_channels" , natural outputChannels)
  ∷ [])

parameterListJSON : ℕ → TensorContext → List JSON
parameterListJSON identifier [] = []
parameterListJSON identifier (parameter ∷ parameters) =
  parameterJSON identifier parameter ∷
  parameterListJSON (suc identifier) parameters

slotIndex : ∀ {P Π} → Slot TensorSignature P Π → ℕ
slotIndex here = zero
slotIndex (there slot) = suc (slotIndex slot)

activationJSON : Activation → JSON
activationJSON relu = string "relu"

fixedKernelJSON :
  ∀ {kernelHeight kernelWidth inputChannels outputChannels} →
  FixedKernel kernelHeight kernelWidth inputChannels outputChannels → JSON
fixedKernelJSON (ncaPerception channels) = object
  ( ("type" , string "nca_perception")
  ∷ ("channels" , natural channels)
  ∷ ("boundary" , string "zero")
  ∷ [])

primitiveJSON : ∀ {Π A B} → BoundPrimitive Π A B → JSON
primitiveJSON
  (BoundPrimitive.linear height width
    inputFeatures outputFeatures parameter) = object
  ( ("type" , string "linear")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("input_features" , natural inputFeatures)
  ∷ ("output_features" , natural outputFeatures)
  ∷ ("parameter" , natural (slotIndex parameter))
  ∷ [])
primitiveJSON
  (BoundPrimitive.convolution height width kernelHeight kernelWidth
    inputChannels outputChannels parameter) = object
  ( ("type" , string "convolution")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("kernel_height" , natural kernelHeight)
  ∷ ("kernel_width" , natural kernelWidth)
  ∷ ("input_channels" , natural inputChannels)
  ∷ ("output_channels" , natural outputChannels)
  ∷ ("parameter" , natural (slotIndex parameter))
  ∷ [])
primitiveJSON
  (BoundPrimitive.fixedConvolution height width kernel) = object
  ( ("type" , string "fixed_convolution")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("kernel" , fixedKernelJSON kernel)
  ∷ [])
primitiveJSON
  (BoundPrimitive.activate height width channels activation) = object
  ( ("type" , string "activation")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("channels" , natural channels)
  ∷ ("activation" , activationJSON activation)
  ∷ [])
primitiveJSON (BoundPrimitive.add height width channels) = object
  ( ("type" , string "add")
  ∷ ("height" , natural height)
  ∷ ("width" , natural width)
  ∷ ("channels" , natural channels)
  ∷ [])

wireTag : ∀ {A B} → DataWire TensorDataflow A B → String
wireTag copyData = "copy"
wireTag discardData = "discard"
wireTag swapData = "swap"
wireTag associateˡ = "associate_left"
wireTag associateʳ = "associate_right"

dataWireJSON : ∀ {A B} → DataWire TensorDataflow A B → JSON
dataWireJSON {A = A} {B = B} wire = object
  ( ("type" , string (wireTag wire))
  ∷ ("input" , shapeJSON A)
  ∷ ("output" , shapeJSON B)
  ∷ [])

operationJSON : ∀ {Π A B} → Operation Π A B → JSON
operationJSON {A = A} identity = object
  ( ("type" , string "identity")
  ∷ ("shape" , shapeJSON A)
  ∷ [])
operationJSON (primitiveOp primitiveCode) = primitiveJSON primitiveCode
operationJSON (sequential first later) = object
  ( ("type" , string "sequential")
  ∷ ("first" , operationJSON first)
  ∷ ("later" , operationJSON later)
  ∷ [])
operationJSON (parallel left right) = object
  ( ("type" , string "parallel")
  ∷ ("left" , operationJSON left)
  ∷ ("right" , operationJSON right)
  ∷ [])
operationJSON (dataWire wire) = dataWireJSON wire
operationJSON (repeat count body) = object
  ( ("type" , string "repeat")
  ∷ ("count" , natural count)
  ∷ ("body" , operationJSON body)
  ∷ [])

versionJSON : Version → JSON
versionJSON v1 = natural 1

documentJSON : ∀ {Π A B} → Document Π A B → JSON
documentJSON {Π = Π} {A = A} {B = B} architecture = object
  ( ("schema" , string "paraforge-architecture")
  ∷ ("version" , versionJSON (version architecture))
  ∷ ("input" , shapeJSON A)
  ∷ ("output" , shapeJSON B)
  ∷ ("parameters" , array (parameterListJSON zero Π))
  ∷ ("operation" , operationJSON (operation architecture))
  ∷ [])

renderDocument : ∀ {Π A B} → Document Π A B → String
renderDocument architecture =
  renderJSON (documentJSON architecture) ++ₛ "\n"

primitiveReferences : ∀ {Π A B} → BoundPrimitive Π A B → List ℕ
primitiveReferences (BoundPrimitive.linear _ _ _ _ parameter) =
  slotIndex parameter ∷ []
primitiveReferences
  (BoundPrimitive.convolution _ _ _ _ _ _ parameter) =
  slotIndex parameter ∷ []
primitiveReferences (BoundPrimitive.fixedConvolution _ _ _) = []
primitiveReferences (BoundPrimitive.activate _ _ _ _) = []
primitiveReferences (BoundPrimitive.add _ _ _) = []

repeatReferences : ℕ → List ℕ → List ℕ
repeatReferences zero references = []
repeatReferences (suc count) references =
  references List.++ repeatReferences count references

operationReferences : ∀ {Π A B} → Operation Π A B → List ℕ
operationReferences identity = []
operationReferences (primitiveOp primitiveCode) =
  primitiveReferences primitiveCode
operationReferences (sequential first later) =
  operationReferences first List.++ operationReferences later
operationReferences (parallel left right) =
  operationReferences left List.++ operationReferences right
operationReferences (dataWire wire) = []
operationReferences (repeat count body) =
  repeatReferences count (operationReferences body)
