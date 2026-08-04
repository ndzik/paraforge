{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.LearningStep where

open import Level using (0ℓ)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Learning.Interface
open import ParaForge.Learning.Parametric
open import ParaForge.Learning.Training
open import ParaForge.Learning.Update
open import ParaForge.Learning.Instance.Integer

-- The explicit reverse rules compose by the chain rule. For weight 2, bias 1,
-- and input 3, the affine intermediate is 7 and the square output is 49.
nonlinear-forward-check :
  evaluate nonlinearAffine (tt , (+ 2 , + 1)) (+ 3) ≡ + 49
nonlinear-forward-check = refl

-- With output feedback 1, square returns intermediate feedback 14. Affine then
-- returns weight signal 3 * 14, bias signal 14, and input feedback 2 * 14.
nonlinear-reverse-chain-check :
  propagate nonlinearAffine (tt , (+ 2 , + 1)) (+ 3) (+ 1) ≡
  ((tt , (+ 42 , + 14)) , + 28)
nonlinear-reverse-chain-check = refl

translationStep :
  TrainingResult ℕ IntegerInterface IntegerInterface IntegerInterface
translationStep = trainStep
  translation
  halfSquaredErrorFeedback
  (integerGradientDescent (+ 1))
  0
  (+ 2)
  (+ 3)
  (+ 8)

translation-output-check : output translationStep ≡ + 5
translation-output-check = refl

translation-feedback-check :
  outputFeedback translationStep ≡ -[1+ 2 ]
translation-feedback-check = refl

translation-parameter-signal-check :
  parameterSignal translationStep ≡ -[1+ 2 ]
translation-parameter-signal-check = refl

translation-input-feedback-check :
  inputFeedback translationStep ≡ -[1+ 2 ]
translation-input-feedback-check = refl

translation-state-check : nextState translationStep ≡ 1
translation-state-check = refl

translation-update-check : nextParameter translationStep ≡ + 5
translation-update-check = refl

translation-updated-output-check :
  evaluate translation (nextParameter translationStep) (+ 3) ≡ + 8
translation-updated-output-check = refl

-- The composed nonlinear learner is trained through the same generic step.
-- Its output feedback is -1, square propagates -4, and affine emits signals
-- -8 and -4 before the separate updater changes weight and bias.
nonlinearStep :
  TrainingResult
    ℕ
    (unitᶠ ⊗ᶠ AffineParameters)
    IntegerInterface
    IntegerInterface
nonlinearStep = trainStep
  nonlinearAffine
  halfSquaredErrorFeedback
  (nonlinearAffineGradientDescent (+ 1))
  0
  (tt , (+ 1 , + 0))
  (+ 2)
  (+ 5)

nonlinear-training-output-check : output nonlinearStep ≡ + 4
nonlinear-training-output-check = refl

nonlinear-training-signal-check :
  parameterSignal nonlinearStep ≡
  (tt , (-[1+ 7 ] , -[1+ 3 ]))
nonlinear-training-signal-check = refl

nonlinear-training-input-feedback-check :
  inputFeedback nonlinearStep ≡ -[1+ 3 ]
nonlinear-training-input-feedback-check = refl

nonlinear-training-state-check : nextState nonlinearStep ≡ 1
nonlinear-training-state-check = refl

nonlinear-training-parameter-check :
  nextParameter nonlinearStep ≡ (tt , (+ 9 , + 4))
nonlinear-training-parameter-check = refl

-- The same learner and feedback source can use a policy that observes credit
-- without updating parameters. Backward propagation prescribes no optimizer.
keptStep :
  TrainingResult
    (⊤ {0ℓ})
    (unitᶠ ⊗ᶠ AffineParameters)
    IntegerInterface
    IntegerInterface
keptStep = trainStep
  nonlinearAffine
  halfSquaredErrorFeedback
  keepParameters
  tt
  (tt , (+ 1 , + 0))
  (+ 2)
  (+ 5)

alternate-policy-check :
  nextParameter keptStep ≡ (tt , (+ 1 , + 0))
alternate-policy-check = refl
