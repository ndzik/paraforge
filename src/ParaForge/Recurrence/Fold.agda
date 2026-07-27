{-# OPTIONS --safe --without-K #-}

module ParaForge.Recurrence.Fold where

-- A folding cell is kept separate from its recursion scheme. The finite fold
-- below reuses one parameter for initialization and every recurrent step.
-- Fixed-length unrollings make that sharing explicit as a G.1-oriented cell
-- from independent parameter positions to their diagonal restriction.

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
import Data.List.Base as List
import Data.Vec.Base as Vec
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization

-- A one-step folding algebra. Its left summand initializes the state; its
-- right summand combines one input with the recursively folded state.
FoldingCell :
  ∀ {o : Level} (p : Level) (A S : Set o) → Set (o ⊔ lsuc p)
FoldingCell {o = o} p A S =
  Para {o = o} {p = p} (⊤ {o} ⊎ (A × S)) S

-- Structural recursion over finite lists. The same parameter is supplied to
-- the base case and to every step, rather than accumulated by recursion.
foldShared :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  Parameters cell → List.List A → S
foldShared cell parameter List.[] =
  run cell (parameter , inj₁ tt)
foldShared cell parameter (input List.∷ inputs) =
  run cell
    (parameter , inj₂ (input , foldShared cell parameter inputs))

-- The recursion scheme itself is again a parameterized map, retaining only
-- the one parameter object belonging to the cell.
foldPara :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  Para {o = o} {p = p} (List.List A) S
foldPara cell = mkPara (Parameters cell) λ where
  (parameter , inputs) → foldShared cell parameter inputs

-- A normalized right-associated product of n + 1 independent copies of P.
-- Zero inputs still require one parameter for the initial-state branch.
ParameterCopies : ∀ {p : Level} → Set p → ℕ → Set p
ParameterCopies P zero = P
ParameterCopies P (suc n) = P × ParameterCopies P n

-- The repeated diagonal selecting the same value at all n + 1 positions.
repeatParameter :
  ∀ {p : Level} {P : Set p} →
  (n : ℕ) → P → ParameterCopies P n
repeatParameter zero parameter = parameter
repeatParameter (suc n) parameter =
  parameter , repeatParameter n parameter

-- An n-step evaluator with independent parameters for initialization and
-- each recurrent application. Vec fixes the input length while the parameter
-- product exposes every position that will later be tied.
foldUntiedEvaluator :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  ParameterCopies (Parameters cell) n × Vec.Vec A n → S
foldUntiedEvaluator cell zero (parameter , Vec.[]) =
  run cell (parameter , inj₁ tt)
foldUntiedEvaluator cell (suc n)
  ((parameter , remainingParameters) , input Vec.∷ remainingInputs) =
  run cell
    ( parameter
    , inj₂
        ( input
        , foldUntiedEvaluator cell n
            (remainingParameters , remainingInputs)
        )
    )

foldUntiedAt :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  Para {o = o} {p = p} (Vec.Vec A n) S
foldUntiedAt cell n =
  mkPara
    (ParameterCopies (Parameters cell) n)
    (foldUntiedEvaluator cell n)

-- The shared fixed-length fold is defined by restricting the untied evaluator
-- along the repeated diagonal. This makes preservation computational.
foldSharedAtEvaluator :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  Parameters cell × Vec.Vec A n → S
foldSharedAtEvaluator cell n (parameter , inputs) =
  foldUntiedEvaluator cell n
    (repeatParameter n parameter , inputs)

foldSharedAt :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  Para {o = o} {p = p} (Vec.Vec A n) S
foldSharedAt cell n =
  mkPara (Parameters cell) (foldSharedAtEvaluator cell n)

foldTyingPreserves :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  ∀ parameter inputs →
  run (foldSharedAt cell n) (parameter , inputs) ≡
  run (foldUntiedAt cell n)
    (repeatParameter n parameter , inputs)
foldTyingPreserves cell n parameter inputs = refl

-- Cell direction: untied ⇒ shared. Its parameter map has the opposite G.1
-- direction P → P^(n+1), copying one target parameter into every source slot.
untiedToSharedAt :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (n : ℕ) →
  Reparameterization
    (foldUntiedAt cell n)
    (foldSharedAt cell n)
untiedToSharedAt cell n = mkReparameterization
  (repeatParameter n)
  (foldTyingPreserves cell n)

vectorToList :
  ∀ {o : Level} {A : Set o} {n : ℕ} →
  Vec.Vec A n → List.List A
vectorToList Vec.[] = List.[]
vectorToList (input Vec.∷ inputs) =
  input List.∷ vectorToList inputs

-- The list recursion and its fixed-length diagonal restriction have the same
-- behavior. Unlike preservation above, the recursive case uses congruence.
foldSharedAt-agrees :
  ∀ {o p : Level} {A S : Set o} →
  (cell : FoldingCell p A S) →
  (parameter : Parameters cell) →
  ∀ {n : ℕ} (inputs : Vec.Vec A n) →
  foldShared cell parameter (vectorToList inputs) ≡
  run (foldSharedAt cell n) (parameter , inputs)
foldSharedAt-agrees cell parameter Vec.[] = refl
foldSharedAt-agrees cell parameter (input Vec.∷ inputs) =
  cong
    (λ state → run cell (parameter , inj₂ (input , state)))
    (foldSharedAt-agrees cell parameter inputs)

-- A small executable folding RNN. The parameter acts as a recurrent bias and
-- also chooses the initial state.
sumCell : FoldingCell 0ℓ ℕ ℕ
sumCell = mkPara ℕ λ where
  (bias , inj₁ _) → bias
  (bias , inj₂ (input , state)) → bias + (input + state)

sampleList : List.List ℕ
sampleList = 2 List.∷ 3 List.∷ List.[]

sampleVector : Vec.Vec ℕ 2
sampleVector = 2 Vec.∷ 3 Vec.∷ Vec.[]

fold-list-evaluates :
  run (foldPara sumCell) (1 , sampleList) ≡ 8
fold-list-evaluates = refl

fold-untied-evaluates :
  run (foldUntiedAt sumCell 2)
    ((10 , (20 , 30)) , sampleVector) ≡ 65
fold-untied-evaluates = refl

sumFoldTying :
  Reparameterization
    (foldUntiedAt sumCell 2)
    (foldSharedAt sumCell 2)
sumFoldTying = untiedToSharedAt sumCell 2

fold-diagonal-evaluates :
  mapParameters sumFoldTying 1 ≡ (1 , (1 , 1))
fold-diagonal-evaluates = refl

fold-shared-evaluates :
  run (foldSharedAt sumCell 2) (1 , sampleVector) ≡ 8
fold-shared-evaluates = refl

fold-sharing-preserves :
  run (foldSharedAt sumCell 2) (1 , sampleVector) ≡
  run (foldUntiedAt sumCell 2)
    (mapParameters sumFoldTying 1 , sampleVector)
fold-sharing-preserves = preserves-run sumFoldTying 1 sampleVector

fold-list-and-fixed-agree :
  foldShared sumCell 1 (vectorToList sampleVector) ≡
  run (foldSharedAt sumCell 2) (1 , sampleVector)
fold-list-and-fixed-agree = foldSharedAt-agrees sumCell 1 sampleVector
