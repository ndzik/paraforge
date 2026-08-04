{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LearningWiring where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Algebra
open import ParaForge.Learning.Lens
open import ParaForge.Learning.Architecture.Wiring
open import ParaForge.Learning.Architecture.Parameter

------------------------------------------------------------------------
-- A closed test signature

data TestInterface : Set where
  atomI   : TestInterface
  oneI    : TestInterface
  tensorI : TestInterface → TestInterface → TestInterface

data TestParameter : Set where
  parameter : TestParameter

data NoPrimitive
  (Γ : List TestParameter)
  (A B : TestInterface) : Set where

data TestReparameterization :
  List TestParameter → List TestParameter → Set where
  doubleParameter : TestReparameterization
    (parameter ∷ []) (parameter ∷ [])

TestSignature : Signature 0ℓ 0ℓ 0ℓ
TestSignature = record
  { InterfaceCode = TestInterface
  ; ParameterCode = TestParameter
  ; PrimitiveCode = NoPrimitive
  ; ReparameterizationCode = TestReparameterization
  ; Shareable = λ _ → ⊤
  }

TestDataflow : DataflowSignature TestSignature
TestDataflow = record
  { unitInterface = oneI
  ; tensorInterface = tensorI
  }

------------------------------------------------------------------------
-- Activation wiring

NatInterface : FeedbackInterface 0ℓ 0ℓ
NatInterface = feedbackInterface ℕ ℕ

natFeedbackMonoid : FeedbackMonoid NatInterface
natFeedbackMonoid = feedbackMonoid
  0
  _+_
  +-assoc
  +-identityˡ
  +-identityʳ

interpretTestInterface : TestInterface → FeedbackInterface 0ℓ 0ℓ
interpretTestInterface atomI = NatInterface
interpretTestInterface oneI = unitᶠ
interpretTestInterface (tensorI A B) =
  interpretTestInterface A ⊗ᶠ interpretTestInterface B

testFeedbackAlgebra :
  (A : TestInterface) → FeedbackMonoid (interpretTestInterface A)
testFeedbackAlgebra atomI = natFeedbackMonoid
testFeedbackAlgebra oneI = unitFeedbackMonoid
testFeedbackAlgebra (tensorI A B) =
  testFeedbackAlgebra A ⊗ᶠᵐ testFeedbackAlgebra B

TestDataflowLearning :
  DataflowLearningModel TestDataflow 0ℓ 0ℓ
TestDataflowLearning = record
  { interpretInterface = interpretTestInterface
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
  ; feedbackAlgebra = testFeedbackAlgebra
  ; tensor-empty-compatible = refl
  ; tensor-combine-compatible = λ _ _ → refl
  }

module DataSemantics = InterpretDataWiring TestDataflowLearning

copyLens : Lens
  (interpretTestInterface atomI)
  (interpretTestInterface (tensorI atomI atomI))
copyLens = DataSemantics.interpretDataWire
  (copyData {A = atomI})

dataIdentityLens : Lens NatInterface NatInterface
dataIdentityLens = idₗ

data-identity-check : forward dataIdentityLens 3 ≡ 3
data-identity-check = refl

copy-forward-check : forward copyLens 3 ≡ (3 , 3)
copy-forward-check = refl

-- Left branch feedback is combined before right branch feedback.
copy-backward-check : backward copyLens (3 , (4 , 5)) ≡ 9
copy-backward-check = refl

discardLens : Lens
  (interpretTestInterface atomI)
  (interpretTestInterface oneI)
discardLens = DataSemantics.interpretDataWire
  (discardData {A = atomI})

discard-forward-check : forward discardLens 7 ≡ tt
discard-forward-check = refl

discard-backward-check : backward discardLens (7 , tt) ≡ 0
discard-backward-check = refl

swapLens : Lens
  (interpretTestInterface (tensorI atomI atomI))
  (interpretTestInterface (tensorI atomI atomI))
swapLens = DataSemantics.interpretDataWire
  (swapData {A = atomI} {B = atomI})

swap-forward-check : forward swapLens (2 , 5) ≡ (5 , 2)
swap-forward-check = refl

swap-backward-check :
  backward swapLens ((2 , 5) , (11 , 13)) ≡ (13 , 11)
swap-backward-check = refl

associateLeftLens : Lens
  (interpretTestInterface (tensorI (tensorI atomI atomI) atomI))
  (interpretTestInterface (tensorI atomI (tensorI atomI atomI)))
associateLeftLens = DataSemantics.interpretDataWire
  (associateˡ {A = atomI} {B = atomI} {C = atomI})

associate-forward-check :
  forward associateLeftLens ((1 , 2) , 3) ≡ (1 , (2 , 3))
associate-forward-check = refl

associate-backward-check :
  backward associateLeftLens (((1 , 2) , 3) , (4 , (5 , 6))) ≡
  ((4 , 5) , 6)
associate-backward-check = refl

associateRightLens : Lens
  (interpretTestInterface (tensorI atomI (tensorI atomI atomI)))
  (interpretTestInterface (tensorI (tensorI atomI atomI) atomI))
associateRightLens = DataSemantics.interpretDataWire
  (associateʳ {A = atomI} {B = atomI} {C = atomI})

associate-right-forward-check :
  forward associateRightLens (1 , (2 , 3)) ≡ ((1 , 2) , 3)
associate-right-forward-check = refl

associate-right-backward-check :
  backward associateRightLens ((1 , (2 , 3)) , ((4 , 5) , 6)) ≡
  (4 , (5 , 6))
associate-right-backward-check = refl

addLens : Lens
  (interpretTestInterface (tensorI atomI atomI))
  (interpretTestInterface atomI)
addLens = lens
  (λ where (left , right) → left + right)
  (λ where (_ , feedback) → feedback , feedback)

-- A residual with an identity transformed branch elaborates to copy followed
-- by addition. Its two branch signals are merged at the copied activation.
identityResidualLens : Lens
  (interpretTestInterface atomI)
  (interpretTestInterface atomI)
identityResidualLens = addLens ∘ₗ copyLens

residual-forward-check : forward identityResidualLens 3 ≡ 6
residual-forward-check = refl

residual-feedback-aggregation-check :
  backward identityResidualLens (3 , 4) ≡ 8
residual-feedback-aggregation-check = refl

------------------------------------------------------------------------
-- Parameter restriction and sharing

ParameterInterface : FeedbackInterface 0ℓ 0ℓ
ParameterInterface = feedbackInterface ℕ (List ℕ)

listFeedbackMonoid : FeedbackMonoid ParameterInterface
listFeedbackMonoid = feedbackMonoid
  []
  _++_
  ++-assoc
  ++-identityˡ
  ++-identityʳ

TestParameterLearning :
  ParameterLearningModel TestSignature 0ℓ 0ℓ
TestParameterLearning = record
  { interpretParameter = λ _ → ParameterInterface
  ; interpretReparameterization = λ where
      doubleParameter → parameterLens
        (λ where
          (value ∷ᶜ []ᶜ) → (value + value) ∷ᶜ []ᶜ)
        (λ where
          (_ ∷ᶜ []ᶜ) (signal ∷ᶜ []ᶜ) →
            (signal ++ signal) ∷ᶜ []ᶜ)
  ; shareableFeedback = λ _ → listFeedbackMonoid
  }

module ParameterSemantics =
  InterpretParameterWiring TestParameterLearning

OneParameter : Context TestSignature
OneParameter = parameter ∷ []

TwoParameters : Context TestSignature
TwoParameters = parameter ∷ parameter ∷ []

ThreeOccurrences : Context TestSignature
ThreeOccurrences = parameter ∷ parameter ∷ parameter ∷ []

oneShareable : AllShareable TestSignature OneParameter
oneShareable = tt ∷ₛ shareable[]

twoShareable : AllShareable TestSignature TwoParameters
twoShareable = tt ∷ₛ tt ∷ₛ shareable[]

duplicatedParameterLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter TwoParameters
duplicatedParameterLens = ParameterSemantics.interpretParamWire
  (copyParameters TestSignature oneShareable)

parameterIdentityLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter OneParameter
parameterIdentityLens = ParameterSemantics.interpretParamWire identity

parameter-identity-check :
  backwardParameters parameterIdentityLens
    (7 ∷ᶜ []ᶜ) ((1 ∷ []) ∷ᶜ []ᶜ) ≡
  (1 ∷ []) ∷ᶜ []ᶜ
parameter-identity-check = refl

parameter-copy-forward-check :
  forwardParameters duplicatedParameterLens (7 ∷ᶜ []ᶜ) ≡
  7 ∷ᶜ 7 ∷ᶜ []ᶜ
parameter-copy-forward-check = refl

parameter-sharing-backward-check :
  backwardParameters duplicatedParameterLens
    (7 ∷ᶜ []ᶜ)
    ((1 ∷ []) ∷ᶜ (2 ∷ []) ∷ᶜ []ᶜ) ≡
  (1 ∷ 2 ∷ []) ∷ᶜ []ᶜ
parameter-sharing-backward-check = refl

tripleSelection :
  Selection TestSignature OneParameter ThreeOccurrences
tripleSelection =
  select here (select here (select here select[]))

tripleParameterLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter ThreeOccurrences
tripleParameterLens = ParameterSemantics.interpretParamWire
  (cartesian oneShareable tripleSelection)

-- The list monoid is deliberately noncommutative, making aggregation order
-- observable: occurrence signals remain first, second, then third.
repeated-selection-order-check :
  backwardParameters tripleParameterLens
    (9 ∷ᶜ []ᶜ)
    ((1 ∷ []) ∷ᶜ (2 ∷ []) ∷ᶜ (3 ∷ []) ∷ᶜ []ᶜ) ≡
  (1 ∷ 2 ∷ 3 ∷ []) ∷ᶜ []ᶜ
repeated-selection-order-check = refl

swapSelection :
  Selection TestSignature TwoParameters TwoParameters
swapSelection = select (there here) (select here select[])

permutationLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    TwoParameters TwoParameters
permutationLens = ParameterSemantics.interpretParamWire
  (cartesian twoShareable swapSelection)

parameter-permutation-forward-check :
  forwardParameters permutationLens (10 ∷ᶜ 20 ∷ᶜ []ᶜ) ≡
  20 ∷ᶜ 10 ∷ᶜ []ᶜ
parameter-permutation-forward-check = refl

parameter-permutation-backward-check :
  backwardParameters permutationLens
    (10 ∷ᶜ 20 ∷ᶜ []ᶜ)
    ((1 ∷ []) ∷ᶜ (2 ∷ []) ∷ᶜ []ᶜ) ≡
  (2 ∷ []) ∷ᶜ (1 ∷ []) ∷ᶜ []ᶜ
parameter-permutation-backward-check = refl

parameterDeletionLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    TwoParameters []
parameterDeletionLens = ParameterSemantics.interpretParamWire
  (discardParameters TestSignature twoShareable)

parameter-deletion-backward-check :
  backwardParameters parameterDeletionLens
    (10 ∷ᶜ 20 ∷ᶜ []ᶜ) []ᶜ ≡
  [] ∷ᶜ [] ∷ᶜ []ᶜ
parameter-deletion-backward-check = refl

generatedParameterLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter OneParameter
generatedParameterLens = ParameterSemantics.interpretParamWire
  (generated doubleParameter)

generated-forward-check :
  forwardParameters generatedParameterLens (4 ∷ᶜ []ᶜ) ≡
  8 ∷ᶜ []ᶜ
generated-forward-check = refl

generated-backward-check :
  backwardParameters generatedParameterLens
    (4 ∷ᶜ []ᶜ) ((5 ∷ []) ∷ᶜ []ᶜ) ≡
  (5 ∷ 5 ∷ []) ∷ᶜ []ᶜ
generated-backward-check = refl

composedParameterLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter OneParameter
composedParameterLens = ParameterSemantics.interpretParamWire
  (generated doubleParameter ∘w identity)

parameter-composition-check :
  backwardParameters composedParameterLens
    (4 ∷ᶜ []ᶜ) ((6 ∷ []) ∷ᶜ []ᶜ) ≡
  (6 ∷ 6 ∷ []) ∷ᶜ []ᶜ
parameter-composition-check = refl

parallelIdentityLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    TwoParameters TwoParameters
parallelIdentityLens = ParameterSemantics.interpretParamWire
  (identity {Γ = OneParameter} ⊗w identity {Γ = OneParameter})

parameter-tensor-check :
  backwardParameters parallelIdentityLens
    (10 ∷ᶜ 20 ∷ᶜ []ᶜ)
    ((1 ∷ []) ∷ᶜ (2 ∷ []) ∷ᶜ []ᶜ) ≡
  (1 ∷ []) ∷ᶜ (2 ∷ []) ∷ᶜ []ᶜ
parameter-tensor-check = refl

rightUnitLens :
  ParameterLens TestSignature
    (ParameterLearningModel.interpretParameter TestParameterLearning)
    OneParameter (OneParameter ++ [])
rightUnitLens = ParameterSemantics.interpretParamWire rightUnit

parameter-right-unit-check :
  backwardParameters rightUnitLens
    (7 ∷ᶜ []ᶜ) ((3 ∷ []) ∷ᶜ []ᶜ) ≡
  (3 ∷ []) ∷ᶜ []ᶜ
parameter-right-unit-check = refl
