{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Parametric where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import ParaForge.Learning.Interface
open import ParaForge.Learning.Lens using (Lens; lens)

private
  variable
    pv pf v f : Level
    P Q : FeedbackInterface pv pf
    A B C : FeedbackInterface v f

-- Parameters are themselves forward/feedback interfaces. Their feedback
-- carrier is an abstract parameter signal, not necessarily a gradient or an
-- updated parameter value.
record ParametricLens
  (P : FeedbackInterface pv pf)
  (A B : FeedbackInterface v f) : Set (pv ⊔ pf ⊔ v ⊔ f) where
  constructor parametricLens
  field
    evaluate  : Value P → Value A → Value B
    propagate :
      Value P → Value A → Feedback B →
      Feedback P × Feedback A

open ParametricLens public

infixr 9 _∘ₚₗ_

-- Parameter-free identity. The unit parameter signal records that no
-- effective parameter received credit.
idₚₗ : ParametricLens (unitᶠ {v = pv} {f = pf}) A A
idₚₗ = parametricLens
  (λ _ input → input)
  (λ _ _ feedback → tt , feedback)

-- Read `later ∘ₚₗ first` from right to left. Parameters and their signals both
-- use the established later-before-earlier order Q × P.
--
-- The backward pass deliberately recomputes the intermediate activation
-- `evaluate first earlierParameter input`. A typed residual/tape can replace
-- this policy later without changing the feedback ordering established here.
_∘ₚₗ_ :
  ∀ {pv pf v f : Level}
    {P Q : FeedbackInterface pv pf}
    {A B C : FeedbackInterface v f} →
  ParametricLens Q B C →
  ParametricLens P A B →
  ParametricLens (Q ⊗ᶠ P) A C
_∘ₚₗ_ {P = P} {Q = Q} {A = A} {C = C} later first =
  parametricLens evaluateComposed propagateComposed
  where
    evaluateComposed : Value (Q ⊗ᶠ P) → Value A → Value C
    evaluateComposed (laterParameter , earlierParameter) input =
      evaluate later laterParameter
        (evaluate first earlierParameter input)

    propagateComposed :
      Value (Q ⊗ᶠ P) → Value A → Feedback C →
      Feedback (Q ⊗ᶠ P) × Feedback A
    propagateComposed (laterParameter , earlierParameter) input feedback
      with propagate later laterParameter
        (evaluate first earlierParameter input) feedback
    ... | laterSignal , intermediateFeedback
      with propagate first earlierParameter input intermediateFeedback
    ... | earlierSignal , inputFeedback =
      (laterSignal , earlierSignal) , inputFeedback

-- Forgetting the parameter boundary gives an ordinary lens whose input pairs
-- parameter values with activation values and whose backward output pairs the
-- corresponding signals.
toLens :
  ParametricLens P A B →
  Lens (P ⊗ᶠ A) B
toLens learner = lens
  (λ where (parameter , input) → evaluate learner parameter input)
  (λ where
    ((parameter , input) , feedback) →
      propagate learner parameter input feedback)
