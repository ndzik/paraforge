{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Interface where

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (_×_)
open import Data.Unit.Polymorphic.Base using (⊤)

-- A learning interface keeps forward values separate from the feedback that
-- can be sent against those values. No duality, equality, or vector-space
-- relationship between the two carriers is assumed.
record FeedbackInterface (v f : Level) : Set (suc (v ⊔ f)) where
  constructor feedbackInterface
  field
    Value    : Set v
    Feedback : Set f

open FeedbackInterface public

private
  variable
    v f : Level

-- Products pair both forward values and backward feedback. The operations
-- needed to aggregate feedback from copied values are intentionally absent:
-- they are additional semantics, not part of a bare feedback interface.
infixr 7 _⊗ᶠ_

_⊗ᶠ_ :
  FeedbackInterface v f →
  FeedbackInterface v f →
  FeedbackInterface v f
A ⊗ᶠ B = feedbackInterface
  (Value A × Value B)
  (Feedback A × Feedback B)

unitᶠ : FeedbackInterface v f
unitᶠ = feedbackInterface ⊤ ⊤
