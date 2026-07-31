{-# OPTIONS --safe --without-K #-}

module ParaForge.Actegory.Strong.Instance.Sets.Monad where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (refl; cong)

open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation
  using (NaturalTransformation; ntHelper)

open import ParaForge.Actegory.Strong.Endofunctor using (Strength)
open import ParaForge.Actegory.Strong.Monad using (StrongMonad)
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory)

private
  variable
    ℓ : Level

-- The exception endofunctor keeps failures fixed and maps successful values.
ExceptionFunctor : Set ℓ → Functor (Sets ℓ) (Sets ℓ)
ExceptionFunctor E = record
  { F₀ = λ X → E ⊎ X
  ; F₁ = λ f → λ where
      (inj₁ error) → inj₁ error
      (inj₂ value) → inj₂ (f value)
  ; identity = λ where
      (inj₁ _) → refl
      (inj₂ _) → refl
  ; homomorphism = λ where
      (inj₁ _) → refl
      (inj₂ _) → refl
  ; F-resp-≈ = λ f≈g → λ where
      (inj₁ _) → refl
      (inj₂ value) → cong inj₂ (f≈g value)
  }

ExceptionUnit :
  (E : Set ℓ) →
  NaturalTransformation id (ExceptionFunctor E)
ExceptionUnit E = ntHelper record
  { η = λ X → inj₂
  ; commute = λ f value → refl
  }

ExceptionJoin :
  (E : Set ℓ) →
  NaturalTransformation
    (ExceptionFunctor E ∘F ExceptionFunctor E)
    (ExceptionFunctor E)
ExceptionJoin E = ntHelper record
  { η = λ X → λ where
      (inj₁ error) → inj₁ error
      (inj₂ result) → result
  ; commute = λ where
      f (inj₁ error) → refl
      f (inj₂ (inj₁ error)) → refl
      f (inj₂ (inj₂ value)) → refl
  }

ExceptionMonad : Set ℓ → Monad (Sets ℓ)
ExceptionMonad E = record
  { F = ExceptionFunctor E
  ; η = ExceptionUnit E
  ; μ = ExceptionJoin E
  ; assoc = λ where
      (inj₁ error) → refl
      (inj₂ (inj₁ error)) → refl
      (inj₂ (inj₂ result)) → refl
  ; sym-assoc = λ where
      (inj₁ error) → refl
      (inj₂ (inj₁ error)) → refl
      (inj₂ (inj₂ result)) → refl
  ; identityˡ = λ where
      (inj₁ error) → refl
      (inj₂ value) → refl
  ; identityʳ = λ result → refl
  }

-- Cartesian strength transports the parameter only through a successful
-- result. An exception carries no computation value to pair with it.
ExceptionStrength :
  (E : Set ℓ) →
  Strength (Sets-Actegory {o = ℓ}) (ExceptionFunctor E)
ExceptionStrength E = record
  { strengthen = ntHelper record
      { η = λ where
          (P , X) → λ where
            (parameter , inj₁ error) → inj₁ error
            (parameter , inj₂ value) → inj₂ (parameter , value)
      ; commute = λ where
          (r , f) (parameter , inj₁ error) → refl
          (r , f) (parameter , inj₂ value) → refl
      }
  ; unit-coherence = λ where
      (_ , inj₁ error) → refl
      (_ , inj₂ value) → refl
  ; associativity-coherence = λ where
      ((_ , _) , inj₁ error) → refl
      ((_ , _) , inj₂ value) → refl
  }

ExceptionStrongMonad :
  Set ℓ → StrongMonad (Sets-Actegory {o = ℓ})
ExceptionStrongMonad E = record
  { monad = ExceptionMonad E
  ; strength = ExceptionStrength E
  ; multiplication-coherence = λ where
      (parameter , inj₁ error) → refl
      (parameter , inj₂ (inj₁ error)) → refl
      (parameter , inj₂ (inj₂ value)) → refl
  ; monad-unit-coherence = λ where
      (parameter , value) → refl
  }
