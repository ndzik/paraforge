{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.Composition where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Para.Set

-- The parameter is interpreted as an offset.
addParameter : Para ℕ ℕ
addParameter = mkPara ℕ λ where
  (offset , input) → offset + input

-- The parameter is interpreted as a scale factor.
scaleParameter : Para ℕ ℕ
scaleParameter = mkPara ℕ λ where
  (factor , input) → factor * input

-- This annotation fixes the otherwise intentionally polymorphic parameter
-- universe of the identity for the concrete examples below.
idℕ : Para {p = 0ℓ} ℕ ℕ
idℕ = idₚ

identity-evaluates : run idℕ (tt , 4) ≡ 4
identity-evaluates = refl

-- Composition stores the outer parameter first: factor, then offset.
-- Remember its `Q × P`, so `P` is the offset, and `Q` is the factor:
-- 3 + 4 = 7 -> 2 * 7 = 14
composition-evaluates :
  run (scaleParameter ∘ₚ addParameter) ((2 , 3) , 4) ≡ 14
composition-evaluates = refl

-- The left and right identity examples do not prove that the complete Para
-- records are equal. `(⊤ × ℕ)` and `(ℕ × ⊤)` are canonically isomorphic, but not
-- definitionally equal!
left-identity-evaluates :
  run (idℕ ∘ₚ addParameter) ((tt , 3) , 4) ≡ 7
left-identity-evaluates = refl

right-identity-evaluates :
  run (addParameter ∘ₚ idℕ) ((3 , tt) , 4) ≡ 7
right-identity-evaluates = refl
