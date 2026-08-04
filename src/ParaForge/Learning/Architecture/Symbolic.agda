{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Symbolic where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core

private
  variable
    i p g : Level
    Σ : Signature i p g

-- Parameter routes retain declared generators as opaque syntax and expose the
-- destinations and repeated destinations of cartesian selections. They do not
-- assume a numerical parameter representation.
data ParameterRoute
  {i p g : Level}
  (Σ : Signature i p g) : Set (p ⊔ g) where
  identityRoute : ParameterRoute Σ
  composeRoute : ParameterRoute Σ → ParameterRoute Σ → ParameterRoute Σ
  tensorRoute : ParameterRoute Σ → ParameterRoute Σ → ParameterRoute Σ
  generatedRoute : ∀ {Δ Γ} →
    ReparameterizationCode Σ Δ Γ → ParameterRoute Σ
  cartesianRoute :
    (destinations aggregationSites : List ℕ) → ParameterRoute Σ
  rightUnitRoute : ParameterRoute Σ

member : ℕ → List ℕ → Bool
member wanted [] = false
member wanted (candidate ∷ rest) with wanted ≟ candidate
... | yes _ = true
... | no _ = member wanted rest

repeatedDestinations : List ℕ → List ℕ
repeatedDestinations = collect []
  where
    collect : List ℕ → List ℕ → List ℕ
    collect seen [] = []
    collect seen (destination ∷ rest) =
      if member destination seen
      then destination ∷ collect seen rest
      else collect (destination ∷ seen) rest

slotDestination :
  ∀ {i p g} {Σ : Signature i p g} {P Γ} →
  Slot Σ P Γ → ℕ
slotDestination here = zero
slotDestination (there slot) = suc (slotDestination slot)

selectionDestinations :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  Selection Σ Δ Γ → List ℕ
selectionDestinations select[] = []
selectionDestinations (select slot rest) =
  slotDestination slot ∷ selectionDestinations rest

parameterRoute :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  ParamWire Σ Δ Γ → ParameterRoute Σ
parameterRoute identity = identityRoute
parameterRoute (later ∘w earlier) =
  composeRoute (parameterRoute later) (parameterRoute earlier)
parameterRoute (left ⊗w right) =
  tensorRoute (parameterRoute left) (parameterRoute right)
parameterRoute (generated code) = generatedRoute code
parameterRoute (cartesian evidence selection) =
  let destinations = selectionDestinations selection
  in cartesianRoute destinations (repeatedDestinations destinations)
parameterRoute rightUnit = rightUnitRoute

-- Primitive and structural events are existentially indexed. A trace can
-- retain the original typed code without erasing it to a backend operation.
data LearningNode
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) : Set (i ⊔ p ⊔ g) where
  primitiveNode : ∀ {Γ A B} →
    PrimitiveCode Σ Γ A B → LearningNode D
  dataNode : ∀ {A B} → DataWire D A B → LearningNode D
  parameterNode : ParameterRoute Σ → LearningNode D

record LearningStructure
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) : Set (i ⊔ p ⊔ g) where
  constructor learningStructure
  field
    forwardNodes : List (LearningNode D)
    reverseNodes : List (LearningNode D)
    parameterRoutes : List (ParameterRoute Σ)

open LearningStructure public

emptyStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D
emptyStructure = learningStructure [] [] []

sequentialStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D → LearningStructure D → LearningStructure D
sequentialStructure first later = learningStructure
  (forwardNodes first ++ forwardNodes later)
  (reverseNodes later ++ reverseNodes first)
  (parameterRoutes later ++ parameterRoutes first)

parallelStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D → LearningStructure D → LearningStructure D
parallelStructure left right = learningStructure
  (forwardNodes left ++ forwardNodes right)
  (reverseNodes left ++ reverseNodes right)
  (parameterRoutes right ++ parameterRoutes left)

restrictStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ}
    {Δ Γ} →
  ParamWire Σ Δ Γ → LearningStructure D → LearningStructure D
restrictStructure wire structure =
  let route = parameterRoute wire
      node = parameterNode route
  in learningStructure
    (node ∷ forwardNodes structure)
    (reverseNodes structure ++ (node ∷ []))
    (route ∷ parameterRoutes structure)

module DescribeArchitecture
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) where

  private
    module S = Signature Σ

    variable
      A B : S.InterfaceCode
      Γ : Context Σ

  describeCore : CoreArch Σ Γ A B → LearningStructure D
  describeCore idA = emptyStructure
  describeCore (primA operation) = learningStructure
    (primitiveNode operation ∷ [])
    (primitiveNode operation ∷ [])
    []
  describeCore (first >>>A later) =
    sequentialStructure (describeCore first) (describeCore later)
  describeCore (restrictA wire architecture) =
    restrictStructure wire (describeCore architecture)

  describeCartesian : CartesianArch D Γ A B → LearningStructure D
  describeCartesian (core architecture) = describeCore architecture
  describeCartesian (first >>>C later) =
    sequentialStructure
      (describeCartesian first)
      (describeCartesian later)
  describeCartesian (left ***C right) =
    parallelStructure
      (describeCartesian left)
      (describeCartesian right)
  describeCartesian (wireC wire) = learningStructure
    (dataNode wire ∷ [])
    (dataNode wire ∷ [])
    []
  describeCartesian (restrictC wire architecture) =
    restrictStructure wire (describeCartesian architecture)

  describeNetwork : Network D Γ A B → LearningStructure D
  describeNetwork architecture =
    restrictStructure (binding architecture)
      (describeCartesian (body architecture))
