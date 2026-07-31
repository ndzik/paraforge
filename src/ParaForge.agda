{-# OPTIONS --safe --without-K #-}

module ParaForge where

-- The root namespace remains the executable concrete API. Generic APIs are
-- re-exported through qualified facades so names such as Para, idₚ, and _∘ₚ_
-- do not become ambiguous.
import ParaForge.Monoidal as GenericMonoidal
module Monoidal = GenericMonoidal

import ParaForge.Actegory as GenericActegory
module Actegory = GenericActegory

open import ParaForge.Para.Set public
  using
    ( Para; mkPara; Parameters; run
    ; identityEvaluator; idₚ; _∘ₚ_
    )

open import ParaForge.Para.Set.Reparameterization public
  using
    ( Reparameterization; mkReparameterization
    ; mapParameters; preserves-run
    ; _≈_; ≈-refl; ≈-sym; ≈-trans; reparameterizationSetoid
    ; id₂; _∘ᵥ_; ∘ᵥ-resp-≈
    ; ∘ᵥ-identityˡ; ∘ᵥ-identityʳ; ∘ᵥ-assoc
    ; _∘ₕ_; ∘ₕ-resp-≈; ∘ₕ-identity; interchange
    )

open import ParaForge.Para.Set.Hom public
  using (Hom)

open import ParaForge.Para.Set.Laws public
  using
    ( unitorˡ; unitorˡ⁻¹; unitorʳ; unitorʳ⁻¹
    ; associator; associator⁻¹
    ; unitorˡ-isoˡ; unitorˡ-isoʳ
    ; unitorʳ-isoˡ; unitorʳ-isoʳ
    ; associator-isoˡ; associator-isoʳ
    ; unitorˡ-natural; unitorʳ-natural; associator-natural
    ; triangle; pentagon
    )

open import ParaForge.Para.Set.Bicategory public
  using (composition; ParaSet)

open import ParaForge.Recurrence.Fold public
  using
    ( FoldingCell; foldShared; foldPara
    ; ParameterCopies; repeatParameter
    ; foldUntiedAt; foldSharedAt
    ; foldTyingPreserves; untiedToSharedAt
    ; vectorToList; foldSharedAt-agrees
    )
