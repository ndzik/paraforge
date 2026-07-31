{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.StrongFolding where

open import Level using (Level; 0ℓ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)

open import ParaForge.Actegory.Strong.Endofunctor
  using (StrongEndofunctor)
open import ParaForge.Actegory.Strong.Instance.Sets
  using
    ( FoldingStrongEndofunctor
    ; UnfoldingStrongEndofunctor
    )
import ParaForge.Para.Actegory as General
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory; toConcrete; fromConcrete)
open import ParaForge.Para.Actegory.Strong.Algebra
  using (Algebra; Coalgebra)
open import ParaForge.Para.Actegory.Strong.Endofunctor
  using (liftPara)
import ParaForge.Para.Set as Concrete
import ParaForge.Recurrence.Fold as Fold

private
  variable
    ℓ : Level
    A S : Set ℓ

-- A Para algebra for 1 + A × - has exactly the folding-cell interface:
--
--   P × (1 + A × S) → S.
FoldingAlgebra : (A S : Set ℓ) → Set _
FoldingAlgebra {ℓ = ℓ} A S =
  Algebra
    {𝒜 = Sets-Actegory {o = ℓ}}
    (FoldingStrongEndofunctor A) S

toFoldingCell :
  ∀ {ℓ} {A S : Set ℓ} →
  FoldingAlgebra A S → Fold.FoldingCell ℓ A S
toFoldingCell = toConcrete

fromFoldingCell :
  ∀ {ℓ} {A S : Set ℓ} →
  Fold.FoldingCell ℓ A S → FoldingAlgebra A S
fromFoldingCell = fromConcrete

folding-cell-roundtrip-run :
  ∀ {ℓ} {A S : Set ℓ} →
  (cell : Fold.FoldingCell ℓ A S) →
  ∀ input →
  Concrete.run (toFoldingCell (fromFoldingCell cell)) input
    ≡ Concrete.run cell input
folding-cell-roundtrip-run cell input = refl

-- The concrete strength and lifted evaluator compute branch by branch.
folding-strength-base :
  StrongEndofunctor.σ (FoldingStrongEndofunctor ℕ) ℕ ℕ
    (1 , inj₁ tt)
    ≡ inj₁ tt
folding-strength-base = refl

folding-strength-step :
  StrongEndofunctor.σ (FoldingStrongEndofunctor ℕ) ℕ ℕ
    (2 , inj₂ (3 , 4))
    ≡ inj₂ (3 , (2 , 4))
folding-strength-step = refl

addParameter : General.Para (Sets-Actegory {o = 0ℓ}) ℕ ℕ
addParameter = General.mkPara ℕ λ where
  (parameter , state) → parameter + state

liftedAdd :
  General.Para
    (Sets-Actegory {o = 0ℓ})
    (⊤ ⊎ (ℕ × ℕ))
    (⊤ ⊎ (ℕ × ℕ))
liftedAdd = liftPara (FoldingStrongEndofunctor ℕ) addParameter

lifted-add-base-evaluates :
  General.run liftedAdd (2 , inj₁ tt) ≡ inj₁ tt
lifted-add-base-evaluates = refl

lifted-add-step-evaluates :
  General.run liftedAdd (2 , inj₂ (3 , 4)) ≡ inj₂ (3 , 6)
lifted-add-step-evaluates = refl

sumAlgebra : FoldingAlgebra ℕ ℕ
sumAlgebra = fromFoldingCell Fold.sumCell

sum-algebra-initializes :
  General.run sumAlgebra (1 , inj₁ tt) ≡ 1
sum-algebra-initializes = refl

sum-algebra-steps :
  General.run sumAlgebra (1 , inj₂ (2 , 3)) ≡ 6
sum-algebra-steps = refl

sum-algebra-recovers-cell :
  ∀ input →
  Concrete.run (toFoldingCell sumAlgebra) input
    ≡ Concrete.run Fold.sumCell input
sum-algebra-recovers-cell input = refl

-- Execute the algebra directly, then compare it pointwise with the established
-- concrete finite-list recursion.
foldAlgebra :
  (algebra : FoldingAlgebra A S) →
  General.Parameters algebra →
  List A → S
foldAlgebra algebra parameter [] =
  General.run algebra (parameter , inj₁ tt)
foldAlgebra algebra parameter (input ∷ inputs) =
  General.run algebra
    (parameter , inj₂ (input , foldAlgebra algebra parameter inputs))

foldAlgebra-agrees :
  (algebra : FoldingAlgebra A S) →
  (parameter : General.Parameters algebra) →
  (inputs : List A) →
  foldAlgebra algebra parameter inputs
    ≡ Fold.foldShared (toFoldingCell algebra) parameter inputs
foldAlgebra-agrees algebra parameter [] = refl
foldAlgebra-agrees algebra parameter (input ∷ inputs) =
  cong
    (λ state →
      General.run algebra (parameter , inj₂ (input , state)))
    (foldAlgebra-agrees algebra parameter inputs)

strong-fold-evaluates :
  foldAlgebra sumAlgebra 1 Fold.sampleList ≡ 8
strong-fold-evaluates = refl

strong-fold-recovers-concrete :
  foldAlgebra sumAlgebra 1 Fold.sampleList
    ≡ Fold.foldShared Fold.sumCell 1 Fold.sampleList
strong-fold-recovers-concrete =
  foldAlgebra-agrees sumAlgebra 1 Fold.sampleList

-- A coalgebra for O × - is a parameterized state machine S → O × S.
UnfoldingCoalgebra : (O S : Set ℓ) → Set _
UnfoldingCoalgebra {ℓ = ℓ} O S =
  Coalgebra
    {𝒜 = Sets-Actegory {o = ℓ}}
    (UnfoldingStrongEndofunctor O) S

counterCoalgebra : UnfoldingCoalgebra ℕ ℕ
counterCoalgebra = General.mkPara ℕ λ where
  (increment , state) → state , increment + state

counter-coalgebra-evaluates :
  General.run counterCoalgebra (2 , 5) ≡ (5 , 7)
counter-coalgebra-evaluates = refl
