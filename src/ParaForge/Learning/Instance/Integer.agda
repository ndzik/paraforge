{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Instance.Integer where

open import Level using (0ℓ)
open import Data.Integer.Base using (ℤ; +_; _+_; _-_; _*_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import ParaForge.Learning.Interface
open import ParaForge.Learning.Lens
open import ParaForge.Learning.Parametric
open import ParaForge.Learning.Training
open import ParaForge.Learning.Update

-- Integers provide deterministic normalization for the reference checks. The
-- reverse rules below are explicit formal polynomial derivatives; this module
-- is not an automatic differentiation implementation.
IntegerInterface : FeedbackInterface 0ℓ 0ℓ
IntegerInterface = feedbackInterface ℤ ℤ

-- A one-parameter translation is convenient for checking a complete update.
translation :
  ParametricLens IntegerInterface IntegerInterface IntegerInterface
translation = parametricLens
  (λ parameter input → parameter + input)
  (λ parameter input feedback → feedback , feedback)

-- Parameters are ordered as weight × bias. Backward propagation returns the
-- corresponding weight × bias signal followed by input feedback.
AffineParameters : FeedbackInterface 0ℓ 0ℓ
AffineParameters = IntegerInterface ⊗ᶠ IntegerInterface

affine :
  ParametricLens AffineParameters IntegerInterface IntegerInterface
affine = parametricLens
  (λ where (weight , bias) input → weight * input + bias)
  (λ where
    (weight , bias) input feedback →
      (input * feedback , feedback) , weight * feedback)

squareLens : Lens IntegerInterface IntegerInterface
squareLens = lens
  (λ input → input * input)
  (λ where (input , feedback) → ((+ 2) * input) * feedback)

square :
  ParametricLens (unitᶠ {v = 0ℓ} {f = 0ℓ})
    IntegerInterface IntegerInterface
square = parameterFree squareLens

-- The parameter order is the unit signal for the later square followed by the
-- earlier affine weight and bias signals.
nonlinearAffine :
  ParametricLens
    (unitᶠ {v = 0ℓ} {f = 0ℓ} ⊗ᶠ AffineParameters)
    IntegerInterface
    IntegerInterface
nonlinearAffine = square ∘ₚₗ affine

-- This is the output derivative of one-half squared error. Keeping it as a
-- FeedbackSource rather than part of the lens leaves other objectives and
-- non-gradient feedback interpretations available.
halfSquaredErrorFeedback : FeedbackSource ℤ IntegerInterface
halfSquaredErrorFeedback = feedbackSource λ prediction target →
  prediction - target

-- A small stateful gradient-descent interpretation. The natural-number state
-- counts update steps; integer arithmetic keeps all example reductions exact.
integerGradientDescent :
  ℤ → UpdatePolicy ℕ IntegerInterface
integerGradientDescent learningRate = updatePolicy λ step parameter signal →
  suc step , parameter - learningRate * signal

integerPairGradientDescent :
  ℤ → UpdatePolicy ℕ AffineParameters
integerPairGradientDescent learningRate = updatePolicy λ where
  step (weight , bias) (weightSignal , biasSignal) →
    suc step ,
    ( weight - learningRate * weightSignal
    , bias - learningRate * biasSignal
    )

nonlinearAffineGradientDescent :
  ℤ → UpdatePolicy ℕ
    (unitᶠ {v = 0ℓ} {f = 0ℓ} ⊗ᶠ AffineParameters)
nonlinearAffineGradientDescent learningRate = updatePolicy λ where
  step (_ , (weight , bias)) (_ , (weightSignal , biasSignal)) →
    suc step ,
    ( tt
    , ( weight - learningRate * weightSignal
      , bias - learningRate * biasSignal
      )
    )
