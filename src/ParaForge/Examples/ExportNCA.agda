{-# OPTIONS --safe --without-K #-}

module ParaForge.Examples.ExportNCA where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Architecture.Export.IR
open import ParaForge.Architecture.Export.Compile
open import ParaForge.Architecture.Export.JSON
open import ParaForge.Examples.NCA

ncaDocument : Document NcaParameters NcaState NcaState
ncaDocument = compileSharedRollout rolloutLength ncaStep

ncaJSON : String
ncaJSON = renderDocument ncaDocument

zero-rollout : Document [] NcaState NcaState
zero-rollout = compileSharedRollout 0 ncaStep

zero-rollout-compiles-to-identity :
  operation zero-rollout ≡ identity
zero-rollout-compiles-to-identity = refl

rollout-compiles-to-explicit-repeat :
  operation ncaDocument ≡
  repeat rolloutLength (operation (compileNetwork ncaStep))
rollout-compiles-to-explicit-repeat = refl

step-parameter-reference-order :
  operationReferences (operation (compileNetwork ncaStep)) ≡
  1 ∷ 0 ∷ []
step-parameter-reference-order = refl

rollout-parameter-reference-order :
  operationReferences (operation ncaDocument) ≡
  1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ []
rollout-parameter-reference-order = refl

expanded-rollout-reference-order :
  operationReferences (operation (compileNetwork ncaRollout)) ≡
  1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ []
expanded-rollout-reference-order = refl

compact-repeat-agrees-with-expanded-references :
  operationReferences (operation ncaDocument) ≡
  operationReferences (operation (compileNetwork ncaRollout))
compact-repeat-agrees-with-expanded-references = refl
