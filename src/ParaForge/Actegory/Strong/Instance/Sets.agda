{-# OPTIONS --safe --without-K #-}

module ParaForge.Actegory.Strong.Instance.Sets where

open import Level using (Level)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Relation.Binary.PropositionalEquality.Core
  using (refl; cong)

open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (ntHelper)

open import ParaForge.Actegory.Strong.Endofunctor
  using (Strength; StrongEndofunctor)
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory)

private
  variable
    ℓ : Level

-- The folding-pattern endofunctor from Example I.1:
--
--   X ↦ 1 + A × X.
FoldingFunctor : Set ℓ → Functor (Sets ℓ) (Sets ℓ)
FoldingFunctor {ℓ = ℓ} A = record
  { F₀ = λ X → ⊤ {ℓ} ⊎ (A × X)
  ; F₁ = λ f → λ where
      (inj₁ unit) → inj₁ unit
      (inj₂ (input , state)) → inj₂ (input , f state)
  ; identity = λ where
      (inj₁ _) → refl
      (inj₂ _) → refl
  ; homomorphism = λ where
      (inj₁ _) → refl
      (inj₂ _) → refl
  ; F-resp-≈ = λ f≈g → λ where
      (inj₁ _) → refl
      (inj₂ (input , state)) →
        cong (λ result → inj₂ (input , result)) (f≈g state)
  }

-- Cartesian strength distributes a parameter over the recursive branch. On
-- the constant branch it forgets that transported parameter; a Para algebra
-- still has its own outer parameter available to its complete structure map.
FoldingStrength :
  (A : Set ℓ) →
  Strength (Sets-Actegory {o = ℓ}) (FoldingFunctor A)
FoldingStrength A = record
  { strengthen = ntHelper record
      { η = λ where
          (P , X) → λ where
            (parameter , inj₁ unit) → inj₁ unit
            (parameter , inj₂ (input , state)) →
              inj₂ (input , (parameter , state))
      ; commute = λ where
          (r , f) (parameter , inj₁ _) → refl
          (r , f) (parameter , inj₂ (input , state)) → refl
      }
  ; unit-coherence = λ where
      (_ , inj₁ _) → refl
      (_ , inj₂ _) → refl
  ; associativity-coherence = λ where
      ((_ , _) , inj₁ _) → refl
      ((_ , _) , inj₂ _) → refl
  }

FoldingStrongEndofunctor :
  Set ℓ → StrongEndofunctor (Sets-Actegory {o = ℓ})
FoldingStrongEndofunctor A = record
  { F = FoldingFunctor A
  ; strength = FoldingStrength A
  }

-- A small coalgebraic checkpoint from Example I.3:
--
--   X ↦ O × X.
UnfoldingFunctor : Set ℓ → Functor (Sets ℓ) (Sets ℓ)
UnfoldingFunctor O = record
  { F₀ = λ X → O × X
  ; F₁ = λ f → λ where
      (output , state) → output , f state
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ f≈g → λ where
      (output , state) →
        cong (λ result → output , result) (f≈g state)
  }

UnfoldingStrength :
  (O : Set ℓ) →
  Strength (Sets-Actegory {o = ℓ}) (UnfoldingFunctor O)
UnfoldingStrength O = record
  { strengthen = ntHelper record
      { η = λ where
          (P , X) → λ where
            (parameter , (output , state)) →
              output , (parameter , state)
      ; commute = λ where
          (r , f) (parameter , (output , state)) → refl
      }
  ; unit-coherence = λ where
      (_ , (_ , _)) → refl
  ; associativity-coherence = λ where
      ((_ , _) , (_ , _)) → refl
  }

UnfoldingStrongEndofunctor :
  Set ℓ → StrongEndofunctor (Sets-Actegory {o = ℓ})
UnfoldingStrongEndofunctor O = record
  { F = UnfoldingFunctor O
  ; strength = UnfoldingStrength O
  }
