{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.StrongException where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import ParaForge.Actegory.Strong.Endofunctor using (Strength)
open import ParaForge.Actegory.Strong.Monad
  using (strongEndofunctor)
open import ParaForge.Actegory.Strong.Instance.Sets.Monad
  using
    ( ExceptionFunctor; ExceptionUnit; ExceptionJoin
    ; ExceptionStrength; ExceptionStrongMonad
    )
import ParaForge.Para.Actegory as General
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory)
open import ParaForge.Para.Actegory.Strong.Endofunctor
  using (liftPara)

private
  exceptionMap :
    ∀ {A B : Set} → (A → B) → ℕ ⊎ A → ℕ ⊎ B
  exceptionMap = Functor.F₁ (ExceptionFunctor ℕ)

  exceptionUnit : ∀ {A : Set} → A → ℕ ⊎ A
  exceptionUnit {A = A} =
    NaturalTransformation.η (ExceptionUnit ℕ) A

  exceptionJoin : ∀ {A : Set} → ℕ ⊎ (ℕ ⊎ A) → ℕ ⊎ A
  exceptionJoin {A = A} =
    NaturalTransformation.η (ExceptionJoin ℕ) A

  exceptionStrength :
    ∀ {P A : Set} → P × (ℕ ⊎ A) → ℕ ⊎ (P × A)
  exceptionStrength {P = P} {A = A} =
    Strength.σ (ExceptionStrength ℕ) P A

unit-evaluates : exceptionUnit 3 ≡ inj₂ 3
unit-evaluates = refl

join-outer-failure-evaluates :
  exceptionJoin {A = ℕ} (inj₁ 1) ≡ inj₁ 1
join-outer-failure-evaluates = refl

join-inner-failure-evaluates :
  exceptionJoin {A = ℕ} (inj₂ (inj₁ 2)) ≡ inj₁ 2
join-inner-failure-evaluates = refl

join-success-evaluates :
  exceptionJoin {A = ℕ} (inj₂ (inj₂ 3)) ≡ inj₂ 3
join-success-evaluates = refl

strength-failure-evaluates :
  exceptionStrength {P = ℕ} {A = ℕ} (2 , inj₁ 3) ≡ inj₁ 3
strength-failure-evaluates = refl

strength-success-evaluates :
  exceptionStrength {P = ℕ} {A = ℕ} (2 , inj₂ 3) ≡ inj₂ (2 , 3)
strength-success-evaluates = refl

-- The two sides of AS3 are executable functions. This pointwise theorem
-- checks every exception/success branch independently of the record field.
as3-left :
  ∀ {P A : Set} →
  P × (ℕ ⊎ (ℕ ⊎ A)) → ℕ ⊎ (P × A)
as3-left input =
  exceptionJoin
    (exceptionMap exceptionStrength
      (exceptionStrength input))

as3-right :
  ∀ {P A : Set} →
  P × (ℕ ⊎ (ℕ ⊎ A)) → ℕ ⊎ (P × A)
as3-right (parameter , result) =
  exceptionStrength (parameter , exceptionJoin result)

as3-evaluates :
  ∀ {P A : Set}
    (input : P × (ℕ ⊎ (ℕ ⊎ A))) →
  as3-left input ≡ as3-right input
as3-evaluates (parameter , inj₁ error) = refl
as3-evaluates (parameter , inj₂ (inj₁ error)) = refl
as3-evaluates (parameter , inj₂ (inj₂ value)) = refl

-- AS4 says transporting a freshly injected value is fresh injection after
-- pairing with the parameter.
as4-left : ∀ {P A : Set} → P × A → ℕ ⊎ (P × A)
as4-left (parameter , value) =
  exceptionStrength (parameter , exceptionUnit value)

as4-right : ∀ {P A : Set} → P × A → ℕ ⊎ (P × A)
as4-right input = exceptionUnit input

as4-evaluates :
  ∀ {P A : Set} (input : P × A) →
  as4-left input ≡ as4-right input
as4-evaluates (parameter , value) = refl

-- Forgetting AS3/AS4 feeds the exact strong endofunctor expected by the
-- Phase 21 Para lift. Failures remain failures; successful values run the
-- original parameterized evaluator.
addParameter : General.Para (Sets-Actegory {o = 0ℓ}) ℕ ℕ
addParameter = General.mkPara ℕ λ where
  (parameter , value) → parameter + value

liftedException :
  General.Para
    (Sets-Actegory {o = 0ℓ})
    (ℕ ⊎ ℕ)
    (ℕ ⊎ ℕ)
liftedException =
  liftPara
    (strongEndofunctor (ExceptionStrongMonad ℕ))
    addParameter

forgotten-lift-failure-evaluates :
  General.run liftedException (2 , inj₁ 3) ≡ inj₁ 3
forgotten-lift-failure-evaluates = refl

forgotten-lift-success-evaluates :
  General.run liftedException (2 , inj₂ 3) ≡ inj₂ 5
forgotten-lift-success-evaluates = refl
