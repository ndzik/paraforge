{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LearningLens where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Learning.Interface
open import ParaForge.Learning.Lens
open import ParaForge.Learning.Parametric

-- Feedback traces make reverse composition order directly observable.
data BackwardStep : Set where
  firstStep secondStep thirdStep : BackwardStep

TraceInterface : FeedbackInterface 0ℓ 0ℓ
TraceInterface = feedbackInterface ℕ (List BackwardStep)

firstLens : Lens TraceInterface TraceInterface
firstLens = lens
  suc
  (λ where (input , trace) → trace ++ (firstStep ∷ []))

secondLens : Lens TraceInterface TraceInterface
secondLens = lens
  (λ input → input + input)
  (λ where (input , trace) → trace ++ (secondStep ∷ []))

thirdLens : Lens TraceInterface TraceInterface
thirdLens = lens
  (λ input → input + 3)
  (λ where (input , trace) → trace ++ (thirdStep ∷ []))

forward-composition-check :
  forward (secondLens ∘ₗ firstLens) 3 ≡ 8
forward-composition-check = refl

-- Although evaluation runs firstLens and then secondLens, feedback records
-- secondLens before firstLens.
reverse-composition-check :
  backward (secondLens ∘ₗ firstLens) (3 , []) ≡
  secondStep ∷ firstStep ∷ []
reverse-composition-check = refl

left-identity-forward-check :
  forward (idₗ ∘ₗ firstLens) 4 ≡ forward firstLens 4
left-identity-forward-check = refl

left-identity-backward-check :
  backward (idₗ ∘ₗ firstLens) (4 , []) ≡
  backward firstLens (4 , [])
left-identity-backward-check = refl

right-identity-forward-check :
  forward (firstLens ∘ₗ idₗ) 4 ≡ forward firstLens 4
right-identity-forward-check = refl

right-identity-backward-check :
  backward (firstLens ∘ₗ idₗ) (4 , []) ≡
  backward firstLens (4 , [])
right-identity-backward-check = refl

associative-forward-check :
  forward ((thirdLens ∘ₗ secondLens) ∘ₗ firstLens) 3 ≡
  forward (thirdLens ∘ₗ (secondLens ∘ₗ firstLens)) 3
associative-forward-check = refl

associative-backward-check :
  backward ((thirdLens ∘ₗ secondLens) ∘ₗ firstLens) (3 , []) ≡
  backward (thirdLens ∘ₗ (secondLens ∘ₗ firstLens)) (3 , [])
associative-backward-check = refl

-- A small asymmetric parameterized example exposes both the Q × P parameter
-- order and the matching Q♭ × P♭ signal order.
ScalarInterface : FeedbackInterface 0ℓ 0ℓ
ScalarInterface = feedbackInterface ℕ ℕ

firstParametric :
  ParametricLens ScalarInterface ScalarInterface ScalarInterface
firstParametric = parametricLens
  (λ parameter input → parameter + input)
  (λ parameter input feedback →
    parameter + feedback , input + feedback)

secondParametric :
  ParametricLens ScalarInterface ScalarInterface ScalarInterface
secondParametric = parametricLens
  (λ parameter input → parameter + input)
  (λ parameter input feedback →
    parameter + feedback , input + feedback)

parameter-order-check :
  evaluate (secondParametric ∘ₚₗ firstParametric) (3 , 2) 4 ≡ 9
parameter-order-check = refl

-- Propagation first recomputes the intermediate value 2 + 4 = 6. The later
-- component returns signal 3 + 5 = 8 and intermediate feedback 6 + 5 = 11;
-- the earlier component then returns signal 2 + 11 = 13 and input feedback
-- 4 + 11 = 15.
parameter-signal-order-check :
  propagate (secondParametric ∘ₚₗ firstParametric) (3 , 2) 4 5 ≡
  ((8 , 13) , 15)
parameter-signal-order-check = refl
