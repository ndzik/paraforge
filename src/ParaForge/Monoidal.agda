{-# OPTIONS --safe --without-K #-}

-- Stable facade for Para built from the tensor self-action of a monoidal
-- category. Import this module qualified alongside ParaForge when using both
-- the generic and concrete APIs, since their core operation names coincide.
module ParaForge.Monoidal where

open import ParaForge.Para.Monoidal public
  using
    ( Para; mkPara; Parameters; run
    ; idₚ; _∘ₚ_
    )

open import ParaForge.Para.Monoidal.Reparameterization public
  using
    ( Reparameterization; mkReparameterization
    ; mapParameters; preserves-run
    ; _≈_; ≈-refl; ≈-sym; ≈-trans; reparameterizationSetoid
    ; id₂; _∘ᵥ_; ∘ᵥ-resp-≈
    ; ∘ᵥ-identityˡ; ∘ᵥ-identityʳ; ∘ᵥ-assoc
    ; _∘ₕ_; ∘ₕ-resp-≈; ∘ₕ-identity; interchange
    )

open import ParaForge.Para.Monoidal.Hom public
  using (Hom)

open import ParaForge.Para.Monoidal.Laws public
  using
    ( unitorˡ; unitorˡ⁻¹; unitorʳ; unitorʳ⁻¹
    ; associator; associator⁻¹
    ; unitorˡ-isoˡ; unitorˡ-isoʳ
    ; unitorʳ-isoˡ; unitorʳ-isoʳ
    ; associator-isoˡ; associator-isoʳ
    ; unitorˡ-natural; unitorʳ-natural; associator-natural
    ; triangle; pentagon
    )

open import ParaForge.Para.Monoidal.Bicategory public
  using (composition; ParaMonoidal)

open import ParaForge.Para.Monoidal.Instance.Sets public
  using
    ( Sets-Monoidal; MonoidalParaSet
    ; toConcrete; fromConcrete
    ; toConcrete-run; fromConcrete-run
    ; toConcreteCell; fromConcreteCell
    ; to-from-cell-map; from-to-cell-map
    ; identity-agrees; composition-agrees
    )
