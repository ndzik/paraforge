{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Instance.Sets where

open import Level using (0ℓ)
open import Data.List.Base using ([]; _++_)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; trans)

open import ParaForge.Architecture.Model
import ParaForge.Para.Set as Concrete
import ParaForge.Para.Set.Reparameterization as ConcreteCells
import ParaForge.Para.Actegory as General
import ParaForge.Para.Actegory.Reparameterization as GeneralCells
open import ParaForge.Para.Actegory.Instance.Sets
  using (Sets-Actegory; fromConcrete; fromConcreteCell)

private
  variable
    A B C D : Interface
    Γ Γ′ Δ Δ′ : ParamCtx

-- This executable checkpoint uses natural numbers as lightweight scalar
-- representatives for vectors and token tensors. Dimensions remain enforced
-- by Interface indices; numerical tensor operations are intentionally not part
-- of the architecture-language gate.
Value : Interface → Set
Value one = ⊤
Value (vector _) = ℕ
Value (tokens _ _) = ℕ
Value (A ⊗ᵢ B) = Value A × Value B

ParameterValue : Parameter → Set
ParameterValue _ = ℕ

SetsArchitecture : ParamCtx → Interface → Interface → Set
SetsArchitecture Γ A B = Env ParameterValue Γ → Value A → Value B

appendEnv :
  ∀ {F : Parameter → Set} {Γ Δ} →
  Env F Γ → Env F Δ → Env F (Γ ++ Δ)
appendEnv ε right = right
appendEnv (value ∷ₑ left) right = value ∷ₑ appendEnv left right

split-appendEnv :
  ∀ {F : Parameter → Set} {Γ Δ}
  (left : Env F Γ) (right : Env F Δ) →
  splitEnv Γ (appendEnv left right) ≡ (left , right)
split-appendEnv ε right = refl
split-appendEnv (value ∷ₑ left) right
  rewrite split-appendEnv left right = refl

runPrimitive : Primitive Γ A B → SetsArchitecture Γ A B
runPrimitive (dense _ _) (parameter ∷ₑ ε) input = parameter + input
runPrimitive (relu _) ε input = input
runPrimitive (softmax _) ε input = input
runPrimitive (layerNorm _ _) (parameter ∷ₑ ε) input = parameter + input
runPrimitive (selfAttention _ _ _) (parameter ∷ₑ ε) input =
  parameter + input
runPrimitive (feedForward _ _ _) (parameter ∷ₑ ε) input =
  parameter + input
runPrimitive (addTokens _ _) ε (left , right) = left + right

runSequential :
  SetsArchitecture Γ A B →
  SetsArchitecture Δ B C →
  SetsArchitecture (Δ ++ Γ) A C
runSequential {Δ = Δ} first later environment input
  with splitEnv Δ environment
... | laterParameters , firstParameters =
  later laterParameters (first firstParameters input)

runParallel :
  SetsArchitecture Γ A B →
  SetsArchitecture Δ C D →
  SetsArchitecture (Δ ++ Γ) (A ⊗ᵢ C) (B ⊗ᵢ D)
runParallel {Δ = Δ} left right environment (leftInput , rightInput)
  with splitEnv Δ environment
... | rightParameters , leftParameters =
  left leftParameters leftInput , right rightParameters rightInput

runDataWire : DataWire A B → SetsArchitecture [] A B
runDataWire copyData ε value = value , value
runDataWire discardData ε _ = tt
runDataWire swapData ε (left , right) = right , left
runDataWire associateˡ ε ((left , middle) , right) =
  left , (middle , right)
runDataWire associateʳ ε (left , (middle , right)) =
  (left , middle) , right

runRestriction :
  ParamWire Δ Γ →
  SetsArchitecture Γ A B →
  SetsArchitecture Δ A B
runRestriction wire architecture environment input =
  architecture (applyWire wire environment) input

-- Every final Sets interpretation is an existing concrete Para(Set) map.
-- Structural ParamWire restriction gives its canonical G.1 cell by
-- precomposition, so the design spike does not introduce new sharing
-- semantics.
toPara : SetsArchitecture Γ A B →
  Concrete.Para {o = 0ℓ} {p = 0ℓ} (Value A) (Value B)
toPara {Γ = Γ} architecture = Concrete.mkPara (Env ParameterValue Γ) λ where
  (environment , input) → architecture environment input

restrictionCell :
  (wire : ParamWire Δ Γ) →
  (architecture : SetsArchitecture Γ A B) →
  ConcreteCells.Reparameterization
    (toPara architecture)
    (toPara (runRestriction wire architecture))
restrictionCell wire architecture =
  ConcreteCells.mkReparameterization (applyWire wire) λ _ _ → refl

horizontalParameters :
  {first : SetsArchitecture Γ A B} →
  {first′ : SetsArchitecture Γ′ A B} →
  {later : SetsArchitecture Δ B C} →
  {later′ : SetsArchitecture Δ′ B C} →
  ConcreteCells.Reparameterization
    (toPara {A = B} {B = C} later)
    (toPara {A = B} {B = C} later′) →
  ConcreteCells.Reparameterization
    (toPara {A = A} {B = B} first)
    (toPara {A = A} {B = B} first′) →
  Env ParameterValue (Δ′ ++ Γ′) →
  Env ParameterValue (Δ ++ Γ)
horizontalParameters {Δ′ = Δ′} laterCell firstCell environment
  with splitEnv Δ′ environment
... | laterParameters , firstParameters =
  appendEnv
    (ConcreteCells.mapParameters laterCell laterParameters)
    (ConcreteCells.mapParameters firstCell firstParameters)

horizontalCell :
  {first : SetsArchitecture Γ A B} →
  {first′ : SetsArchitecture Γ′ A B} →
  {later : SetsArchitecture Δ B C} →
  {later′ : SetsArchitecture Δ′ B C} →
  (laterCell : ConcreteCells.Reparameterization
    (toPara {A = B} {B = C} later)
    (toPara {A = B} {B = C} later′)) →
  (firstCell : ConcreteCells.Reparameterization
    (toPara {A = A} {B = B} first)
    (toPara {A = A} {B = B} first′)) →
  ConcreteCells.Reparameterization
    (toPara {A = A} {B = C} (runSequential first later))
    (toPara {A = A} {B = C} (runSequential first′ later′))
horizontalCell {Δ′ = Δ′} {first = first} {first′ = first′}
  {later = later} {later′ = later′} laterCell firstCell =
  ConcreteCells.mkReparameterization
    (horizontalParameters laterCell firstCell)
    preserves
  where
    preserves : ∀ environment input →
      runSequential first′ later′ environment input ≡
      runSequential first later
        (horizontalParameters laterCell firstCell environment) input
    preserves environment input with splitEnv Δ′ environment
    ... | laterParameters , firstParameters
      rewrite split-appendEnv
        (ConcreteCells.mapParameters laterCell laterParameters)
        (ConcreteCells.mapParameters firstCell firstParameters) = trans
          (ConcreteCells.preserves-run laterCell laterParameters
            (first′ firstParameters input))
          (cong
            (later (ConcreteCells.mapParameters laterCell laterParameters))
            (ConcreteCells.preserves-run firstCell firstParameters input))

-- The same checkpoint enters the generic Para(M ↷ C) implementation through
-- the established component-preserving Sets specialization.
toGenericPara : SetsArchitecture Γ A B →
  General.Para (Sets-Actegory {o = 0ℓ}) (Value A) (Value B)
toGenericPara architecture = fromConcrete (toPara architecture)

genericRestrictionCell :
  (wire : ParamWire Δ Γ) →
  (architecture : SetsArchitecture Γ A B) →
  GeneralCells.Reparameterization (Sets-Actegory {o = 0ℓ})
    (toGenericPara architecture)
    (toGenericPara (runRestriction wire architecture))
genericRestrictionCell wire architecture =
  fromConcreteCell (restrictionCell wire architecture)

SetsModel : Model
SetsModel = record
  { Architecture = SetsArchitecture
  ; identity = λ where ε input → input
  ; interpretPrimitive = runPrimitive
  ; sequential = runSequential
  ; parallel = runParallel
  ; dataWire = runDataWire
  ; restrict = runRestriction
  }
