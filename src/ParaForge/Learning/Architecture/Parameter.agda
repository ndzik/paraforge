{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Parameter where

open import Level using (Level; suc; _⊔_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Algebra

private
  variable
    p x : Level
    Code : Set p

-- Heterogeneous contexts keep each parameter code tied to its own carrier.
data ContextEnv
  {p x : Level}
  {Code : Set p}
  (F : Code → Set x) : List Code → Set (p ⊔ x) where
  []ᶜ  : ContextEnv F []
  _∷ᶜ_ : ∀ {P Γ} →
    F P → ContextEnv F Γ → ContextEnv F (P ∷ Γ)

infixr 5 _∷ᶜ_

appendContextEnv :
  ∀ {p x} {Code : Set p} {F : Code → Set x} {Γ Δ} →
  ContextEnv F Γ → ContextEnv F Δ → ContextEnv F (Γ ++ Δ)
appendContextEnv []ᶜ right = right
appendContextEnv (value ∷ᶜ left) right =
  value ∷ᶜ appendContextEnv left right

splitContextEnv :
  ∀ {p x} {Code : Set p} {F : Code → Set x}
    (Γ : List Code) {Δ} →
  ContextEnv F (Γ ++ Δ) → ContextEnv F Γ × ContextEnv F Δ
splitContextEnv [] environment = []ᶜ , environment
splitContextEnv (_ ∷ Γ) (value ∷ᶜ environment)
  with splitContextEnv Γ environment
... | left , right = (value ∷ᶜ left) , right

lookupContextEnv :
  ∀ {i p g x} {Σ : Signature i p g}
    {F : ParameterCode Σ → Set x} {P Γ} →
  Slot Σ P Γ → ContextEnv F Γ → F P
lookupContextEnv here (value ∷ᶜ _) = value
lookupContextEnv (there slot) (_ ∷ᶜ rest) =
  lookupContextEnv slot rest

ValueContext :
  ∀ {i p g pv pf} (Σ : Signature i p g) →
  (ParameterCode Σ → FeedbackInterface pv pf) →
  Context Σ → Set (p ⊔ pv)
ValueContext Σ interpretation =
  ContextEnv (λ code → Value (interpretation code))

FeedbackContext :
  ∀ {i p g pv pf} (Σ : Signature i p g) →
  (ParameterCode Σ → FeedbackInterface pv pf) →
  Context Σ → Set (p ⊔ pf)
FeedbackContext Σ interpretation =
  ContextEnv (λ code → Feedback (interpretation code))

-- A reparameterization is interpreted as a parameter lens. Its reverse map may
-- depend on the external parameter value, so declared generators can express
-- nonlinear or otherwise value-dependent transports without changing syntax.
record ParameterLens
  {i p g pv pf : Level}
  (Σ : Signature i p g)
  (interpretation : ParameterCode Σ → FeedbackInterface pv pf)
  (Δ Γ : Context Σ) : Set (p ⊔ g ⊔ pv ⊔ pf) where
  constructor parameterLens
  field
    forwardParameters :
      ValueContext Σ interpretation Δ →
      ValueContext Σ interpretation Γ

    backwardParameters :
      ValueContext Σ interpretation Δ →
      FeedbackContext Σ interpretation Γ →
      FeedbackContext Σ interpretation Δ

open ParameterLens public

record ParameterLearningModel
  {i p g : Level}
  (Σ : Signature i p g)
  (pv pf : Level) : Set (suc (i ⊔ p ⊔ g ⊔ pv ⊔ pf)) where
  private
    module S = Signature Σ

  field
    interpretParameter :
      S.ParameterCode → FeedbackInterface pv pf

    interpretReparameterization : ∀ {Δ Γ} →
      S.ReparameterizationCode Δ Γ →
      ParameterLens Σ interpretParameter Δ Γ

    shareableFeedback : ∀ {P} →
      S.Shareable P → FeedbackMonoid (interpretParameter P)

open ParameterLearningModel public

identityParameterLens :
  ∀ {i p g pv pf} {Σ : Signature i p g}
    {I : ParameterCode Σ → FeedbackInterface pv pf} {Γ} →
  ParameterLens Σ I Γ Γ
identityParameterLens = parameterLens (λ values → values) (λ _ signals → signals)

composeParameterLens :
  ∀ {i p g pv pf} {Σ : Signature i p g}
    {I : ParameterCode Σ → FeedbackInterface pv pf}
    {Θ Δ Γ} →
  ParameterLens Σ I Δ Γ →
  ParameterLens Σ I Θ Δ →
  ParameterLens Σ I Θ Γ
composeParameterLens later earlier = parameterLens
  (λ values → forwardParameters later (forwardParameters earlier values))
  (λ values signals → backwardParameters earlier values
    (backwardParameters later (forwardParameters earlier values) signals))

tensorParameterLens :
  ∀ {i p g pv pf} {Σ : Signature i p g}
    {I : ParameterCode Σ → FeedbackInterface pv pf}
    {Δ Θ Γ Λ} →
  ParameterLens Σ I Δ Γ →
  ParameterLens Σ I Θ Λ →
  ParameterLens Σ I (Δ ++ Θ) (Γ ++ Λ)
tensorParameterLens
  {Σ = Σ} {I = I} {Δ = Δ} {Θ = Θ} {Γ = Γ} {Λ = Λ}
  left right = parameterLens forwardTensor backwardTensor
  where
    forwardTensor :
      ValueContext Σ I (Δ ++ Θ) → ValueContext Σ I (Γ ++ Λ)
    forwardTensor values with splitContextEnv Δ values
    ... | leftValues , rightValues = appendContextEnv
      (forwardParameters left leftValues)
      (forwardParameters right rightValues)

    backwardTensor :
      ValueContext Σ I (Δ ++ Θ) →
      FeedbackContext Σ I (Γ ++ Λ) →
      FeedbackContext Σ I (Δ ++ Θ)
    backwardTensor values signals
      with splitContextEnv Δ values | splitContextEnv Γ signals
    ... | leftValues , rightValues | leftSignals , rightSignals =
      appendContextEnv
        (backwardParameters left leftValues leftSignals)
        (backwardParameters right rightValues rightSignals)

module InterpretParameterWiring
  {i p g pv pf : Level}
  {Σ : Signature i p g}
  (M : ParameterLearningModel Σ pv pf) where

  private
    module S = Signature Σ
    module M = ParameterLearningModel M

    variable
      P : S.ParameterCode
      Γ Δ : Context Σ

  applySelection :
    Selection Σ Δ Γ →
    ValueContext Σ M.interpretParameter Δ →
    ValueContext Σ M.interpretParameter Γ
  applySelection select[] values = []ᶜ
  applySelection (select slot rest) values =
    lookupContextEnv slot values ∷ᶜ applySelection rest values

  emptyParameterFeedback :
    AllShareable Σ Δ →
    FeedbackContext Σ M.interpretParameter Δ
  emptyParameterFeedback shareable[] = []ᶜ
  emptyParameterFeedback (evidence ∷ₛ rest) =
    emptyFeedback (M.shareableFeedback evidence) ∷ᶜ
    emptyParameterFeedback rest

  insertParameterFeedback :
    AllShareable Σ Δ →
    Slot Σ P Δ →
    Feedback (M.interpretParameter P) →
    FeedbackContext Σ M.interpretParameter Δ →
    FeedbackContext Σ M.interpretParameter Δ
  insertParameterFeedback (evidence ∷ₛ rest) here signal
    (current ∷ᶜ signals) =
    _<>ᶠ_ (M.shareableFeedback evidence) signal current ∷ᶜ signals
  insertParameterFeedback (_ ∷ₛ rest) (there slot) signal
    (current ∷ᶜ signals) =
    current ∷ᶜ insertParameterFeedback rest slot signal signals

  aggregateSelection :
    (evidence : AllShareable Σ Δ) →
    (selection : Selection Σ Δ Γ) →
    FeedbackContext Σ M.interpretParameter Γ →
    FeedbackContext Σ M.interpretParameter Δ
  aggregateSelection evidence select[] []ᶜ =
    emptyParameterFeedback evidence
  aggregateSelection evidence (select slot rest) (signal ∷ᶜ signals) =
    insertParameterFeedback evidence slot signal
      (aggregateSelection evidence rest signals)

  selectionParameterLens :
    (evidence : AllShareable Σ Δ) →
    (selection : Selection Σ Δ Γ) →
    ParameterLens Σ M.interpretParameter Δ Γ
  selectionParameterLens evidence selection = parameterLens
    (applySelection selection)
    (λ _ signals → aggregateSelection evidence selection signals)

  rightUnitParameterLens :
    ParameterLens Σ M.interpretParameter Γ (Γ ++ [])
  rightUnitParameterLens {Γ = Γ} = parameterLens
    (λ values → appendContextEnv values []ᶜ)
    (λ _ signals → proj₁ (splitContextEnv Γ signals))

  interpretParamWire :
    ParamWire Σ Δ Γ →
    ParameterLens Σ M.interpretParameter Δ Γ
  interpretParamWire identity = identityParameterLens
  interpretParamWire (later ∘w earlier) =
    composeParameterLens
      (interpretParamWire later)
      (interpretParamWire earlier)
  interpretParamWire (left ⊗w right) =
    tensorParameterLens
      (interpretParamWire left)
      (interpretParamWire right)
  interpretParamWire (generated code) =
    M.interpretReparameterization code
  interpretParamWire (cartesian evidence selection) =
    selectionParameterLens evidence selection
  interpretParamWire rightUnit = rightUnitParameterLens
