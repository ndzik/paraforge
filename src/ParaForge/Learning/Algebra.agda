{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Algebra where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong₂)

open import ParaForge.Learning.Interface

private
  variable
    v f : Level
    A B : FeedbackInterface v f

-- Feedback from copied uses is merged by an explicit monoid. Commutativity is
-- intentionally absent: aggregation retains the left-to-right occurrence
-- order unless a model separately proves that order irrelevant.
record FeedbackMonoid
  (A : FeedbackInterface v f) : Set f where
  constructor feedbackMonoid
  infixl 6 _<>ᶠ_
  field
    emptyFeedback : Feedback A
    _<>ᶠ_ : Feedback A → Feedback A → Feedback A

    <>ᶠ-assoc : ∀ left middle right →
      (left <>ᶠ middle) <>ᶠ right ≡
      left <>ᶠ (middle <>ᶠ right)

    <>ᶠ-identityˡ : ∀ feedback →
      emptyFeedback <>ᶠ feedback ≡ feedback

    <>ᶠ-identityʳ : ∀ feedback →
      feedback <>ᶠ emptyFeedback ≡ feedback

open FeedbackMonoid public

-- Permutation-invariant aggregation is an additional property. Wiring
-- interpretation never assumes it merely because a feedback monoid exists.
record CommutativeFeedback
  {v f : Level}
  {A : FeedbackInterface v f}
  (M : FeedbackMonoid A) : Set f where
  field
    <>ᶠ-comm : ∀ left right →
      _<>ᶠ_ M left right ≡ _<>ᶠ_ M right left

open CommutativeFeedback public

unitFeedbackMonoid :
  FeedbackMonoid (unitᶠ {v = v} {f = f})
unitFeedbackMonoid = feedbackMonoid
  tt
  (λ _ _ → tt)
  (λ _ _ _ → refl)
  (λ _ → refl)
  (λ _ → refl)

infixr 7 _⊗ᶠᵐ_

-- Product feedback aggregates componentwise without exchanging branch order.
_⊗ᶠᵐ_ :
  FeedbackMonoid A → FeedbackMonoid B →
  FeedbackMonoid (A ⊗ᶠ B)
left ⊗ᶠᵐ right = feedbackMonoid
  (emptyFeedback left , emptyFeedback right)
  (λ where
    (left₁ , right₁) (left₂ , right₂) →
      _<>ᶠ_ left left₁ left₂ , _<>ᶠ_ right right₁ right₂)
  (λ where
    (left₁ , right₁) (left₂ , right₂) (left₃ , right₃) →
      cong₂ _,_
        (<>ᶠ-assoc left left₁ left₂ left₃)
        (<>ᶠ-assoc right right₁ right₂ right₃))
  (λ where
    (leftFeedback , rightFeedback) →
      cong₂ _,_
        (<>ᶠ-identityˡ left leftFeedback)
        (<>ᶠ-identityˡ right rightFeedback))
  (λ where
    (leftFeedback , rightFeedback) →
      cong₂ _,_
        (<>ᶠ-identityʳ left leftFeedback)
        (<>ᶠ-identityʳ right rightFeedback))
