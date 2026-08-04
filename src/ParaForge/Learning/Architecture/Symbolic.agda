{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Symbolic where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
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

-- A normalized destination map exposes where every occurrence signal returns.
-- `nothing` is retained for signature-declared generators whose backward map is
-- intentionally opaque to the generic structural interpretation.
contextDestinations :
  ∀ {i p g} {Σ : Signature i p g} →
  ℕ → Context Σ → List (Maybe ℕ)
contextDestinations {Σ = Σ} offset [] = []
contextDestinations {Σ = Σ} offset (_ ∷ Γ) =
  just offset ∷ contextDestinations {Σ = Σ} (suc offset) Γ

unknownDestinations :
  ∀ {i p g} {Σ : Signature i p g} →
  Context Σ → List (Maybe ℕ)
unknownDestinations {Σ = Σ} [] = []
unknownDestinations {Σ = Σ} (_ ∷ Γ) =
  nothing ∷ unknownDestinations {Σ = Σ} Γ

lookupDestination : ℕ → List (Maybe ℕ) → Maybe ℕ
lookupDestination zero [] = nothing
lookupDestination zero (destination ∷ _) = destination
lookupDestination (suc index) [] = nothing
lookupDestination (suc index) (_ ∷ destinations) =
  lookupDestination index destinations

substituteDestinations :
  List (Maybe ℕ) → List (Maybe ℕ) → List (Maybe ℕ)
substituteDestinations outer [] = []
substituteDestinations outer (nothing ∷ rest) =
  nothing ∷ substituteDestinations outer rest
substituteDestinations outer (just index ∷ rest) =
  lookupDestination index outer ∷ substituteDestinations outer rest

shiftDestinations : ℕ → List (Maybe ℕ) → List (Maybe ℕ)
shiftDestinations offset [] = []
shiftDestinations offset (nothing ∷ rest) =
  nothing ∷ shiftDestinations offset rest
shiftDestinations offset (just index ∷ rest) =
  just (offset + index) ∷ shiftDestinations offset rest

externalContext :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  ParamWire Σ Δ Γ → Context Σ
externalContext {Δ = Δ} _ = Δ

occurrenceContext :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  ParamWire Σ Δ Γ → Context Σ
occurrenceContext {Γ = Γ} _ = Γ

parameterDestinations :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  ParamWire Σ Δ Γ → List (Maybe ℕ)
parameterDestinations {Σ = Σ} wire@identity =
  contextDestinations {Σ = Σ} zero (occurrenceContext wire)
parameterDestinations (later ∘w earlier) =
  substituteDestinations
    (parameterDestinations earlier)
    (parameterDestinations later)
parameterDestinations (left ⊗w right) =
  parameterDestinations left ++
  shiftDestinations
    (length (externalContext left))
    (parameterDestinations right)
parameterDestinations {Σ = Σ} wire@(generated _) =
  unknownDestinations {Σ = Σ} (occurrenceContext wire)
parameterDestinations {Σ = Σ} (cartesian evidence selection) =
  knownSelectionDestinations {Σ = Σ} selection
  where
    knownSelectionDestinations :
      ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
      Selection Σ Δ Γ → List (Maybe ℕ)
    knownSelectionDestinations {Σ = Σ} select[] = []
    knownSelectionDestinations {Σ = Σ} (select slot rest) =
      just (slotDestination slot) ∷
      knownSelectionDestinations {Σ = Σ} rest
parameterDestinations {Σ = Σ} wire@rightUnit =
  contextDestinations {Σ = Σ} zero (occurrenceContext wire)

knownDestinations : List (Maybe ℕ) → List ℕ
knownDestinations [] = []
knownDestinations (nothing ∷ rest) = knownDestinations rest
knownDestinations (just destination ∷ rest) =
  destination ∷ knownDestinations rest

parameterAggregationSites :
  ∀ {i p g} {Σ : Signature i p g} {Δ Γ} →
  ParamWire Σ Δ Γ → List ℕ
parameterAggregationSites wire =
  repeatedDestinations (knownDestinations (parameterDestinations wire))

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
    destinationMaps : List (List (Maybe ℕ))
    aggregationMaps : List (List ℕ)

open LearningStructure public

emptyStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D
emptyStructure = learningStructure [] [] [] [] []

sequentialStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D → LearningStructure D → LearningStructure D
sequentialStructure first later = learningStructure
  (forwardNodes first ++ forwardNodes later)
  (reverseNodes later ++ reverseNodes first)
  (parameterRoutes later ++ parameterRoutes first)
  (destinationMaps later ++ destinationMaps first)
  (aggregationMaps later ++ aggregationMaps first)

parallelStructure :
  ∀ {i p g} {Σ : Signature i p g} {D : DataflowSignature Σ} →
  LearningStructure D → LearningStructure D → LearningStructure D
parallelStructure left right = learningStructure
  (forwardNodes left ++ forwardNodes right)
  (reverseNodes left ++ reverseNodes right)
  (parameterRoutes right ++ parameterRoutes left)
  (destinationMaps right ++ destinationMaps left)
  (aggregationMaps right ++ aggregationMaps left)

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
    (parameterDestinations wire ∷ destinationMaps structure)
    (parameterAggregationSites wire ∷ aggregationMaps structure)

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
    []
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
    []
    []
  describeCartesian (restrictC wire architecture) =
    restrictStructure wire (describeCartesian architecture)

  describeNetwork : Network D Γ A B → LearningStructure D
  describeNetwork architecture =
    restrictStructure (binding architecture)
      (describeCartesian (body architecture))
