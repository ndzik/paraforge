{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Model where

open import Level using (Level; suc; _⊔_)
open import Data.List.Base using ([]; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import ParaForge.Architecture.Signature
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Lens
open import ParaForge.Learning.Parametric
open import ParaForge.Learning.Architecture.Wiring
open import ParaForge.Learning.Architecture.Parameter

-- A context-indexed learner is the architecture-level form of ParametricLens.
-- Heterogeneous parameter contexts remain visible in its type instead of being
-- erased into a backend-specific parameter container.
record ArchitectureLearner
  {i p g pv pf v f : Level}
  (Σ : Signature i p g)
  (interfaces : InterfaceCode Σ → FeedbackInterface v f)
  (parameters : ParameterCode Σ → FeedbackInterface pv pf)
  (Γ : Context Σ)
  (A B : InterfaceCode Σ) : Set (i ⊔ p ⊔ g ⊔ pv ⊔ pf ⊔ v ⊔ f) where
  constructor architectureLearner
  field
    evaluateArchitecture :
      ValueContext Σ parameters Γ →
      Value (interfaces A) →
      Value (interfaces B)

    propagateArchitecture :
      ValueContext Σ parameters Γ →
      Value (interfaces A) →
      Feedback (interfaces B) →
      FeedbackContext Σ parameters Γ × Feedback (interfaces A)

open ArchitectureLearner public

contextInterface :
  ∀ {i p g pv pf} (Σ : Signature i p g)
    (parameters : ParameterCode Σ → FeedbackInterface pv pf)
    (Γ : Context Σ) →
  FeedbackInterface (p ⊔ pv) (p ⊔ pf)
contextInterface Σ parameters Γ = feedbackInterface
  (ValueContext Σ parameters Γ)
  (FeedbackContext Σ parameters Γ)

toParametricLens :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {interfaces : InterfaceCode Σ → FeedbackInterface v f}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {Γ A B} →
  ArchitectureLearner Σ interfaces parameters Γ A B →
  ParametricLens
    (contextInterface Σ parameters Γ)
    (interfaces A)
    (interfaces B)
toParametricLens learner = parametricLens
  (evaluateArchitecture learner)
  (propagateArchitecture learner)

emptyArchitectureFeedback :
  ∀ {i p g pv pf} {Σ : Signature i p g}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf} →
  FeedbackContext Σ parameters []
emptyArchitectureFeedback = []ᶜ

identityArchitecture :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {interfaces : InterfaceCode Σ → FeedbackInterface v f}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {A} →
  ArchitectureLearner Σ interfaces parameters [] A A
identityArchitecture {Σ = Σ} {parameters = parameters} = architectureLearner
  (λ []ᶜ input → input)
  (λ []ᶜ _ feedback →
    emptyArchitectureFeedback {Σ = Σ} {parameters = parameters} , feedback)

sequentialArchitecture :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {interfaces : InterfaceCode Σ → FeedbackInterface v f}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {Γ Δ A B C} →
  ArchitectureLearner Σ interfaces parameters Γ A B →
  ArchitectureLearner Σ interfaces parameters Δ B C →
  ArchitectureLearner Σ interfaces parameters (Δ ++ Γ) A C
sequentialArchitecture {Δ = Δ} first later = architectureLearner
  (λ parameters input →
    let parameterParts = splitContextEnv Δ parameters
        laterParameters = proj₁ parameterParts
        firstParameters = proj₂ parameterParts
    in evaluateArchitecture later laterParameters
      (evaluateArchitecture first firstParameters input))
  (λ parameters input feedback →
    let parameterParts = splitContextEnv Δ parameters
        laterParameters = proj₁ parameterParts
        firstParameters = proj₂ parameterParts
        intermediate = evaluateArchitecture first firstParameters input
        laterResult = propagateArchitecture later
          laterParameters intermediate feedback
        firstResult = propagateArchitecture first firstParameters
          input (proj₂ laterResult)
    in appendContextEnv (proj₁ laterResult) (proj₁ firstResult) ,
       proj₂ firstResult)

parallelArchitecture :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {D : DataflowSignature Σ}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {Γ Δ A B C E} →
  (dataflow : DataflowLearningModel D v f) →
  ArchitectureLearner Σ
    (interpretInterface dataflow) parameters Γ A B →
  ArchitectureLearner Σ
    (interpretInterface dataflow) parameters Δ C E →
  ArchitectureLearner Σ
    (interpretInterface dataflow) parameters (Δ ++ Γ)
    (tensorInterface D A C)
    (tensorInterface D B E)
parallelArchitecture {Δ = Δ} dataflow left right = architectureLearner
  (λ parameters input →
    let parameterParts = splitContextEnv Δ parameters
        inputParts = untensorValue dataflow input
    in tensorValue dataflow
      ( evaluateArchitecture left
          (proj₂ parameterParts) (proj₁ inputParts)
      , evaluateArchitecture right
          (proj₁ parameterParts) (proj₂ inputParts)
      ))
  (λ parameters input feedback →
    let parameterParts = splitContextEnv Δ parameters
        inputParts = untensorValue dataflow input
        feedbackParts = untensorFeedback dataflow feedback
        leftResult = propagateArchitecture left
          (proj₂ parameterParts) (proj₁ inputParts) (proj₁ feedbackParts)
        rightResult = propagateArchitecture right
          (proj₁ parameterParts) (proj₂ inputParts) (proj₂ feedbackParts)
    in appendContextEnv (proj₁ rightResult) (proj₁ leftResult) ,
       tensorFeedback dataflow (proj₂ leftResult , proj₂ rightResult))

parameterFreeArchitecture :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {interfaces : InterfaceCode Σ → FeedbackInterface v f}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {A B} →
  Lens (interfaces A) (interfaces B) →
  ArchitectureLearner Σ interfaces parameters [] A B
parameterFreeArchitecture
  {Σ = Σ} {parameters = parameters} operation = architectureLearner
  (λ []ᶜ input → forward operation input)
  (λ []ᶜ input feedback →
    emptyArchitectureFeedback {Σ = Σ} {parameters = parameters} ,
    backward operation (input , feedback))

restrictArchitecture :
  ∀ {i p g pv pf v f}
    {Σ : Signature i p g}
    {interfaces : InterfaceCode Σ → FeedbackInterface v f}
    {parameters : ParameterCode Σ → FeedbackInterface pv pf}
    {Δ Γ A B} →
  ParameterLens Σ parameters Δ Γ →
  ArchitectureLearner Σ interfaces parameters Γ A B →
  ArchitectureLearner Σ interfaces parameters Δ A B
restrictArchitecture restriction learner = architectureLearner
  (λ parameters input → evaluateArchitecture learner
    (forwardParameters restriction parameters) input)
  (λ parameters input feedback →
    let occurrenceParameters = forwardParameters restriction parameters
        result = propagateArchitecture learner
          occurrenceParameters input feedback
    in backwardParameters restriction parameters (proj₁ result) ,
       proj₂ result)

-- The fold depends only on typed carriers and supplied primitive semantics.
-- Numerical backends may choose any internal representation behind these
-- functions; no backend-specific array, differentiation, or runtime concept is
-- exposed here.
record ArchitectureLearningModel
  {i p g : Level}
  (Σ : Signature i p g)
  (D : DataflowSignature Σ)
  (pv pf v f : Level) :
  Set (suc (i ⊔ p ⊔ g ⊔ pv ⊔ pf ⊔ v ⊔ f)) where
  field
    dataflowLearning : DataflowLearningModel D v f
    parameterLearning : ParameterLearningModel Σ pv pf

    primitiveLearning : ∀ {Γ A B} →
      PrimitiveCode Σ Γ A B →
      ArchitectureLearner Σ
        (interpretInterface dataflowLearning)
        (interpretParameter parameterLearning)
        Γ A B

open ArchitectureLearningModel public
