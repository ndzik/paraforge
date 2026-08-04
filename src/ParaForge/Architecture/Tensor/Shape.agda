{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Tensor.Shape where

open import Data.Nat.Base using (ℕ)

-- Numerical tensor shapes and structural products share one interface code,
-- but remain distinct constructors. In particular, _×ˢ_ is split-input
-- parallelism; it does not concatenate or otherwise reshape tensor axes.
data Shape : Set where
  unit   : Shape
  scalar : Shape
  vector : (features : ℕ) → Shape
  grid   : (height width channels : ℕ) → Shape
  _×ˢ_   : Shape → Shape → Shape

infixr 7 _×ˢ_
