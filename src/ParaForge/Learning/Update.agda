{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Update where

open import Level using (Level; 0ℓ; _⊔_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ParaForge.Learning.Interface

private
  variable
    o pv pf : Level
    O : Set o
    P : FeedbackInterface pv pf

-- An update policy interprets a parameter signal. It is deliberately separate
-- from backward propagation and may carry state such as a step counter,
-- momentum, or another optimizer-specific accumulator.
record UpdatePolicy
  (O : Set o)
  (P : FeedbackInterface pv pf) : Set (o ⊔ pv ⊔ pf) where
  constructor updatePolicy
  field
    applyUpdate :
      O → Value P → Feedback P →
      O × Value P

open UpdatePolicy public

-- Lift a stateless interpretation of parameter signals into an update policy.
statelessUpdate :
  (Value P → Feedback P → Value P) →
  UpdatePolicy (⊤ {0ℓ}) P
statelessUpdate update = updatePolicy λ _ parameter signal →
  tt , update parameter signal

-- A valid alternative interpretation is to observe a signal without changing
-- the parameter. This is useful for evaluation and demonstrates that backward
-- propagation does not itself prescribe an optimizer.
keepParameters : UpdatePolicy (⊤ {0ℓ}) P
keepParameters = statelessUpdate λ parameter _ → parameter
