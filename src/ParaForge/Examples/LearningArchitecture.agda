{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LearningArchitecture where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core
open import ParaForge.Architecture.Transformation
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Algebra
open import ParaForge.Learning.Architecture.Wiring
open import ParaForge.Learning.Architecture.Parameter
open import ParaForge.Learning.Architecture.Model
open import ParaForge.Learning.Architecture.Interpretation
open import ParaForge.Learning.Architecture.Symbolic

------------------------------------------------------------------------
-- A tiny backend-neutral signature

data TestInterface : Set where
  scalarI : TestInterface
  unitI   : TestInterface
  pairI   : TestInterface → TestInterface → TestInterface

data TestParameter : Set where
  scalarP : TestParameter

data Stage : Set where
  firstStage secondStage residualStage : Stage

data Primitive :
  List TestParameter → TestInterface → TestInterface → Set where
  shift : Stage → Primitive
    (scalarP ∷ []) scalarI scalarI
  add : Primitive [] (pairI scalarI scalarI) scalarI

data NoReparameterization
  (Δ Γ : List TestParameter) : Set where

TestSignature : Signature 0ℓ 0ℓ 0ℓ
TestSignature = record
  { InterfaceCode = TestInterface
  ; ParameterCode = TestParameter
  ; PrimitiveCode = Primitive
  ; ReparameterizationCode = NoReparameterization
  ; Shareable = λ _ → ⊤
  }

TestDataflow : DataflowSignature TestSignature
TestDataflow = record
  { unitInterface = unitI
  ; tensorInterface = pairI
  }

------------------------------------------------------------------------
-- Abstract feedback events, not numerical derivatives

data FeedbackEvent : Set where
  seed : FeedbackEvent
  activationEvent : Stage → FeedbackEvent
  parameterEvent : Stage → FeedbackEvent
  addLeft addRight : FeedbackEvent

EventFeedback : FeedbackInterface 0ℓ 0ℓ
EventFeedback = feedbackInterface ℕ (List FeedbackEvent)

eventMonoid : FeedbackMonoid EventFeedback
eventMonoid = feedbackMonoid
  []
  _++_
  ++-assoc
  ++-identityˡ
  ++-identityʳ

testInterfaceSemantics : TestInterface → FeedbackInterface 0ℓ 0ℓ
testInterfaceSemantics scalarI = EventFeedback
testInterfaceSemantics unitI = unitᶠ
testInterfaceSemantics (pairI A B) =
  testInterfaceSemantics A ⊗ᶠ testInterfaceSemantics B

interfaceFeedback :
  (A : TestInterface) → FeedbackMonoid (testInterfaceSemantics A)
interfaceFeedback scalarI = eventMonoid
interfaceFeedback unitI = unitFeedbackMonoid
interfaceFeedback (pairI A B) =
  interfaceFeedback A ⊗ᶠᵐ interfaceFeedback B

TestDataflowLearning :
  DataflowLearningModel TestDataflow 0ℓ 0ℓ
TestDataflowLearning = record
  { interpretInterface = testInterfaceSemantics
  ; unitValue = tt
  ; unitValue-unique = λ where tt → refl
  ; tensorValue = λ pair → pair
  ; untensorValue = λ pair → pair
  ; tensorFeedback = λ pair → pair
  ; untensorFeedback = λ pair → pair
  ; untensor-tensor-value = λ _ _ → refl
  ; tensor-untensor-value = λ _ → refl
  ; untensor-tensor-feedback = λ _ _ → refl
  ; tensor-untensor-feedback = λ _ → refl
  ; feedbackAlgebra = interfaceFeedback
  ; tensor-empty-compatible = refl
  ; tensor-combine-compatible = λ _ _ → refl
  }

ParameterInterface : FeedbackInterface 0ℓ 0ℓ
ParameterInterface = feedbackInterface ℕ (List FeedbackEvent)

TestParameterLearning :
  ParameterLearningModel TestSignature 0ℓ 0ℓ
TestParameterLearning = record
  { interpretParameter = λ _ → ParameterInterface
  ; interpretReparameterization = λ ()
  ; shareableFeedback = λ _ → eventMonoid
  }

emptyParameterSignals :
  FeedbackContext TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning) []
emptyParameterSignals = []ᶜ

primitiveLearner : ∀ {Γ A B} →
  Primitive Γ A B →
  ArchitectureLearner TestSignature
    testInterfaceSemantics
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    Γ A B
primitiveLearner (shift stage) = architectureLearner
  (λ where (parameter ∷ᶜ []ᶜ) input → parameter + input)
  (λ where
    (_ ∷ᶜ []ᶜ) _ feedback →
      (parameterEvent stage ∷ []) ∷ᶜ []ᶜ ,
      feedback ++ (activationEvent stage ∷ []))
primitiveLearner add = architectureLearner
  (λ where []ᶜ (left , right) → left + right)
  (λ where
    []ᶜ _ feedback → emptyParameterSignals ,
      ( feedback ++ (addLeft ∷ [])
      , feedback ++ (addRight ∷ [])
      ))

TestLearningModel :
  ArchitectureLearningModel TestSignature TestDataflow
    0ℓ 0ℓ 0ℓ 0ℓ
TestLearningModel = record
  { dataflowLearning = TestDataflowLearning
  ; parameterLearning = TestParameterLearning
  ; primitiveLearning = primitiveLearner
  }

module Learn = InterpretArchitecture TestLearningModel
module Describe = DescribeArchitecture TestDataflow

------------------------------------------------------------------------
-- Shared sequential network

OneParameter : Context TestSignature
OneParameter = scalarP ∷ []

TwoOccurrences : Context TestSignature
TwoOccurrences = scalarP ∷ scalarP ∷ []

oneShareable : AllShareable TestSignature OneParameter
oneShareable = tt ∷ₛ shareable[]

twoShiftBody : CartesianArch TestDataflow
  TwoOccurrences scalarI scalarI
twoShiftBody =
  primC TestDataflow (shift firstStage) >>>C
  primC TestDataflow (shift secondStage)

sharedTwoShift : CartesianArch TestDataflow
  OneParameter scalarI scalarI
sharedTwoShift = restrictC
  (copyParameters TestSignature oneShareable)
  twoShiftBody

sharedTwoShiftCell : ArchitectureCell TestDataflow
  twoShiftBody sharedTwoShift
sharedTwoShiftCell = restrictionCell
  (copyParameters TestSignature oneShareable)

twoShiftNetwork : Network TestDataflow
  OneParameter scalarI scalarI
twoShiftNetwork = network
  TwoOccurrences
  twoShiftBody
  (copyParameters TestSignature oneShareable)

twoShiftLearner : ArchitectureLearner TestSignature
  testInterfaceSemantics
  (ParameterLearningModel.interpretParameter TestParameterLearning)
  OneParameter scalarI scalarI
twoShiftLearner = Learn.interpretNetwork twoShiftNetwork

directTwoShift : ℕ → ℕ → ℕ
directTwoShift parameter input =
  parameter + (parameter + input)

forward-agrees-with-direct : ∀ parameter input →
  evaluateArchitecture twoShiftLearner
    (parameter ∷ᶜ []ᶜ) input ≡
  directTwoShift parameter input
forward-agrees-with-direct parameter input = refl

shared-forward-check :
  evaluateArchitecture twoShiftLearner (2 ∷ᶜ []ᶜ) 3 ≡ 7
shared-forward-check = refl

shared-reverse-order-check :
  propagateArchitecture twoShiftLearner
    (2 ∷ᶜ []ᶜ) 3 (seed ∷ []) ≡
  ( (parameterEvent secondStage ∷ parameterEvent firstStage ∷ [])
      ∷ᶜ []ᶜ
  , seed ∷ activationEvent secondStage ∷
      activationEvent firstStage ∷ []
  )
shared-reverse-order-check = refl

cellParameterTransport :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter TwoOccurrences
cellParameterTransport =
  Learn.interpretCellParameters sharedTwoShiftCell

cell-backward-transport-check :
  backwardParameters cellParameterTransport
    (2 ∷ᶜ []ᶜ)
    ((parameterEvent secondStage ∷ []) ∷ᶜ
      (parameterEvent firstStage ∷ []) ∷ᶜ []ᶜ) ≡
  (parameterEvent secondStage ∷ parameterEvent firstStage ∷ [])
    ∷ᶜ []ᶜ
cell-backward-transport-check = refl

------------------------------------------------------------------------
-- Residual structure derived from copy, parallel, identity, and add

residualBody : CartesianArch TestDataflow
  OneParameter scalarI scalarI
residualBody =
  wireC (copyData {A = scalarI}) >>>C
  ((primC TestDataflow (shift residualStage) ***C
      idC TestDataflow) >>>C
    primC TestDataflow add)

residualNetwork : Network TestDataflow
  OneParameter scalarI scalarI
residualNetwork = network OneParameter residualBody identity

residualLearner : ArchitectureLearner TestSignature
  testInterfaceSemantics
  (ParameterLearningModel.interpretParameter TestParameterLearning)
  OneParameter scalarI scalarI
residualLearner = Learn.interpretNetwork residualNetwork

residual-forward-check :
  evaluateArchitecture residualLearner (2 ∷ᶜ []ᶜ) 3 ≡ 8
residual-forward-check = refl

residual-reverse-check :
  propagateArchitecture residualLearner
    (2 ∷ᶜ []ᶜ) 3 (seed ∷ []) ≡
  ( (parameterEvent residualStage ∷ []) ∷ᶜ []ᶜ
  , seed ∷ addLeft ∷ activationEvent residualStage ∷
      seed ∷ addRight ∷ []
  )
residual-reverse-check = refl

------------------------------------------------------------------------
-- Backend-independent structural description of the same source network

twoShiftStructure : LearningStructure TestDataflow
twoShiftStructure = Describe.describeNetwork twoShiftNetwork

sharingRoute : ParameterRoute TestSignature
sharingRoute = cartesianRoute (0 ∷ 0 ∷ []) (0 ∷ [])

symbolic-forward-order-check :
  forwardNodes twoShiftStructure ≡
  parameterNode sharingRoute ∷
  primitiveNode (shift firstStage) ∷
  primitiveNode (shift secondStage) ∷ []
symbolic-forward-order-check = refl

symbolic-reverse-order-check :
  reverseNodes twoShiftStructure ≡
  primitiveNode (shift secondStage) ∷
  primitiveNode (shift firstStage) ∷
  parameterNode sharingRoute ∷ []
symbolic-reverse-order-check = refl

symbolic-sharing-destinations-check :
  parameterRoutes twoShiftStructure ≡ sharingRoute ∷ []
symbolic-sharing-destinations-check = refl
