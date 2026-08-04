{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Instance.Neural where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (refl)

import ParaForge.Architecture.Model as Neural
open import ParaForge.Architecture.Interpretation
import ParaForge.Architecture.Instance.Symbolic as ExistingSymbolic
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Algebra
open import ParaForge.Learning.Architecture.Wiring
open import ParaForge.Learning.Architecture.Parameter
open import ParaForge.Learning.Architecture.Model

-- These events describe reverse routing only. They are deliberately not
-- gradients, cotangents, VJPs, or update instructions.
data NeuralFeedbackEvent : Set where
  primitiveReverse : ExistingSymbolic.Node → NeuralFeedbackEvent
  parameterReverse : ExistingSymbolic.Node → NeuralFeedbackEvent
  leftResidual rightResidual : NeuralFeedbackEvent

EventFeedback : FeedbackInterface 0ℓ 0ℓ
EventFeedback = feedbackInterface ℕ (List NeuralFeedbackEvent)

eventFeedbackMonoid : FeedbackMonoid EventFeedback
eventFeedbackMonoid = feedbackMonoid
  []
  _++_
  ++-assoc
  ++-identityˡ
  ++-identityʳ

neuralInterface : Neural.Interface → FeedbackInterface 0ℓ 0ℓ
neuralInterface Neural.one = unitᶠ
neuralInterface (Neural.vector _) = EventFeedback
neuralInterface (Neural.tokens _ _) = EventFeedback
neuralInterface (left Neural.⊗ᵢ right) =
  neuralInterface left ⊗ᶠ neuralInterface right

neuralFeedbackMonoid :
  (A : Neural.Interface) → FeedbackMonoid (neuralInterface A)
neuralFeedbackMonoid Neural.one = unitFeedbackMonoid
neuralFeedbackMonoid (Neural.vector _) = eventFeedbackMonoid
neuralFeedbackMonoid (Neural.tokens _ _) = eventFeedbackMonoid
neuralFeedbackMonoid (left Neural.⊗ᵢ right) =
  neuralFeedbackMonoid left ⊗ᶠᵐ neuralFeedbackMonoid right

NeuralDataflowLearning :
  DataflowLearningModel NeuralDataflow 0ℓ 0ℓ
NeuralDataflowLearning = record
  { interpretInterface = neuralInterface
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
  ; feedbackAlgebra = neuralFeedbackMonoid
  ; tensor-empty-compatible = refl
  ; tensor-combine-compatible = λ _ _ → refl
  }

ParameterFeedback : FeedbackInterface 0ℓ 0ℓ
ParameterFeedback = feedbackInterface ℕ (List NeuralFeedbackEvent)

NeuralParameterLearning :
  ParameterLearningModel NeuralSignature 0ℓ 0ℓ
NeuralParameterLearning = record
  { interpretParameter = λ _ → ParameterFeedback
  ; interpretReparameterization = λ ()
  ; shareableFeedback = λ _ → eventFeedbackMonoid
  }

emptyParameterFeedback :
  FeedbackContext NeuralSignature
    (interpretParameter NeuralParameterLearning) []
emptyParameterFeedback = []ᶜ

parameterizedVectorReverse :
  ∀ {P inputWidth outputWidth}
    (node : ExistingSymbolic.Node) →
  (ℕ → ℕ → ℕ) →
  ArchitectureLearner NeuralSignature neuralInterface
    (interpretParameter NeuralParameterLearning)
    (P ∷ [])
    (Neural.vector inputWidth)
    (Neural.vector outputWidth)
parameterizedVectorReverse node run = architectureLearner
  (λ where (parameter ∷ᶜ []ᶜ) input → run parameter input)
  (λ where
    (_ ∷ᶜ []ᶜ) _ feedback →
      (parameterReverse node ∷ []) ∷ᶜ []ᶜ ,
      feedback ++ (primitiveReverse node ∷ []))

parameterFreeVectorReverse :
  ∀ {inputWidth outputWidth}
    (node : ExistingSymbolic.Node) →
  (ℕ → ℕ) →
  ArchitectureLearner NeuralSignature neuralInterface
    (interpretParameter NeuralParameterLearning)
    []
    (Neural.vector inputWidth)
    (Neural.vector outputWidth)
parameterFreeVectorReverse node run = architectureLearner
  (λ where []ᶜ input → run input)
  (λ where
    []ᶜ _ feedback → emptyParameterFeedback ,
      feedback ++ (primitiveReverse node ∷ []))

parameterizedTokenReverse :
  ∀ {P sequenceLength modelWidth}
    (node : ExistingSymbolic.Node) →
  (ℕ → ℕ → ℕ) →
  ArchitectureLearner NeuralSignature neuralInterface
    (interpretParameter NeuralParameterLearning)
    (P ∷ [])
    (Neural.tokens sequenceLength modelWidth)
    (Neural.tokens sequenceLength modelWidth)
parameterizedTokenReverse node run = architectureLearner
  (λ where (parameter ∷ᶜ []ᶜ) input → run parameter input)
  (λ where
    (_ ∷ᶜ []ᶜ) _ feedback →
      (parameterReverse node ∷ []) ∷ᶜ []ᶜ ,
      feedback ++ (primitiveReverse node ∷ []))

neuralPrimitiveLearning : ∀ {Γ A B} →
  Neural.Primitive Γ A B →
  ArchitectureLearner NeuralSignature neuralInterface
    (interpretParameter NeuralParameterLearning)
    Γ A B
neuralPrimitiveLearning (Neural.dense inputWidth outputWidth) =
  parameterizedVectorReverse
    (ExistingSymbolic.denseNode inputWidth outputWidth)
    _+_
neuralPrimitiveLearning (Neural.relu width) =
  parameterFreeVectorReverse
    (ExistingSymbolic.reluNode width) (λ input → input)
neuralPrimitiveLearning (Neural.softmax width) =
  parameterFreeVectorReverse
    (ExistingSymbolic.softmaxNode width) (λ input → input)
neuralPrimitiveLearning
  (Neural.layerNorm sequenceLength modelWidth) =
  parameterizedTokenReverse
    (ExistingSymbolic.layerNormNode sequenceLength modelWidth)
    _+_
neuralPrimitiveLearning
  (Neural.selfAttention sequenceLength modelWidth heads) =
  parameterizedTokenReverse
    (ExistingSymbolic.attentionNode sequenceLength modelWidth heads)
    _+_
neuralPrimitiveLearning
  (Neural.feedForward sequenceLength modelWidth hiddenWidth) =
  parameterizedTokenReverse
    (ExistingSymbolic.feedForwardNode
      sequenceLength modelWidth hiddenWidth)
    _+_
neuralPrimitiveLearning (Neural.addTokens sequenceLength modelWidth) =
  architectureLearner
    (λ where []ᶜ (left , right) → left + right)
    (λ where
      []ᶜ _ feedback → emptyParameterFeedback ,
        ( feedback ++ (leftResidual ∷ [])
        , feedback ++ (rightResidual ∷ [])
        ))

NeuralLearningModel :
  ArchitectureLearningModel NeuralSignature NeuralDataflow
    0ℓ 0ℓ 0ℓ 0ℓ
NeuralLearningModel = record
  { dataflowLearning = NeuralDataflowLearning
  ; parameterLearning = NeuralParameterLearning
  ; primitiveLearning = neuralPrimitiveLearning
  }
