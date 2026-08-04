{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Training where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import ParaForge.Learning.Interface
open import ParaForge.Learning.Parametric
open import ParaForge.Learning.Update

private
  variable
    t o pv pf v f : Level
    T : Set t
    O : Set o
    P : FeedbackInterface pv pf
    A B : FeedbackInterface v f

-- A feedback source closes the output boundary of a learner. Targets are kept
-- independent from output values: they may instead be rewards, constraints,
-- corrections, or another source of typed feedback.
record FeedbackSource
  (T : Set t)
  (B : FeedbackInterface v f) : Set (t ⊔ v ⊔ f) where
  constructor feedbackSource
  field
    feedbackFor : Value B → T → Feedback B

open FeedbackSource public

-- A training result exposes every stage of one pure update. Keeping these
-- observations explicit makes reference semantics and future symbolic traces
-- testable without relying on effects or a runtime training loop.
record TrainingResult
  (O : Set o)
  (P : FeedbackInterface pv pf)
  (A B : FeedbackInterface v f) : Set (o ⊔ pv ⊔ pf ⊔ v ⊔ f) where
  constructor trainingResult
  field
    output          : Value B
    outputFeedback  : Feedback B
    parameterSignal : Feedback P
    inputFeedback   : Feedback A
    nextState       : O
    nextParameter   : Value P

open TrainingResult public

private
  finishTraining :
    ∀ {t o pv pf v f : Level}
      {T : Set t} {O : Set o}
      {P : FeedbackInterface pv pf}
      {A B : FeedbackInterface v f} →
    ParametricLens P A B →
    FeedbackSource T B →
    UpdatePolicy O P →
    O → Value P → Value A → T → Value B →
    TrainingResult O P A B
  finishTraining learner source updater state parameter input target result
    with feedbackFor source result target
  ... | outputSignal with propagate learner parameter input outputSignal
  ... | parameterCredit , inputCredit
    with applyUpdate updater state parameter parameterCredit
  ... | updatedState , updatedParameter = trainingResult
    result
    outputSignal
    parameterCredit
    inputCredit
    updatedState
    updatedParameter

-- One step has three explicit stages: evaluate, propagate feedback, then
-- interpret the resulting parameter signal through an update policy.
trainStep :
  ParametricLens P A B →
  FeedbackSource T B →
  UpdatePolicy O P →
  O → Value P → Value A → T →
  TrainingResult O P A B
trainStep learner source updater state parameter input target =
  finishTraining learner source updater state parameter input target
    (evaluate learner parameter input)
