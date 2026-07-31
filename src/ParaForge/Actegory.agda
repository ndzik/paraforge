{-# OPTIONS --safe --without-K #-}

-- Stable facade for Para built from a coherent action of a monoidal parameter
-- category on a computation category.
module ParaForge.Actegory where

open import ParaForge.Actegory.Core public
  using
    ( Actegory; action; _⊙₀_; _⊙₁_
    ; unitAction; tensorAction; nestedAction
    ; unitorˡ-coherence; tensorSelfAction
    )
  renaming
    ( unitor to actionUnitor
    ; associator to actionAssociator
    ; triangle to actionTriangle
    ; pentagon to actionPentagon
    )

open import ParaForge.Actegory.Strong.Endofunctor public
  using
    ( strengthSource; strengthTarget
    ; Strength; StrongEndofunctor
    ; strengthen; σ
    ; unit-coherence; associativity-coherence
    ; strength-natural-id
    )
  renaming
    ( F to endofunctor
    ; strength to endofunctorStrength
    )

open import ParaForge.Para.Actegory public
  using
    ( Para; mkPara; Parameters; run
    ; idₚ; _∘ₚ_
    )

open import ParaForge.Para.Actegory.Strong.Algebra public
  using (Algebra; Coalgebra)

open import ParaForge.Para.Actegory.Strong.Endofunctor public
  using
    ( liftPara; lift-preserves
    ; liftCell; liftCell-id; liftCell-compose; liftCell-resp-≈
    ; liftHom; lift-composition-run; lift-identity-run
    ; identity-comparison; identity-comparison⁻¹
    ; composition-comparison; composition-comparison⁻¹
    ; lift-restriction-run; lift-sharing-run
    ; liftPseudofunctor
    )

open import ParaForge.Para.Actegory.Reparameterization public
  using
    ( Reparameterization; mkReparameterization
    ; mapParameters; preserves-run
    ; _≈_; ≈-refl; ≈-sym; ≈-trans; reparameterizationSetoid
    ; id₂; _∘ᵥ_; ∘ᵥ-resp-≈
    ; ∘ᵥ-identityˡ; ∘ᵥ-identityʳ; ∘ᵥ-assoc
    ; _∘ₕ_; ∘ₕ-resp-≈; ∘ₕ-identity; interchange
    )

open import ParaForge.Para.Actegory.Restriction public
  using
    ( restrictParameters; restrictCell
    ; restrict-identity-run; restrict-identity-comparison
    ; restrict-identity-cell
    ; restrict-compose-run; restrict-compose-comparison
    ; restrict-compose-cell
    ; restrict-horizontal-run; restrict-horizontal-comparison
    ; restrict-horizontal-cell
    )

open import ParaForge.Para.Actegory.Sharing public
  using
    ( ParameterComonoid
    ; copyParameter; discardParameter
    ; copyParameter3ˡ; copyParameter3ʳ; copyParameter3-coherent
    ; dropLeftParameter; dropRightParameter
    ; dropLeft-copy; dropRight-copy
    ; CocommutativeParameter; swappedCopyParameter
    ; counitalCopyComonoid; counitalCopy-cocommutative
    ; untiedParameterPair; tieParameterPair; tieParameterPairCell
    ; untiedParameterTriple
    ; tieParameterTriple; tieParameterTripleAlternative
    ; tieParameterTriple-run-coherent
    ; tieParameterPairSwapped; tieParameterPair-commutative-run
    )

open import ParaForge.Para.Actegory.Hom public
  using (Hom)

open import ParaForge.Para.Actegory.Laws public
  using
    ( unitorˡ; unitorˡ⁻¹; unitorʳ; unitorʳ⁻¹
    ; associator; associator⁻¹
    ; unitorˡ-isoˡ; unitorˡ-isoʳ
    ; unitorʳ-isoˡ; unitorʳ-isoʳ
    ; associator-isoˡ; associator-isoʳ
    ; unitorˡ-natural; unitorʳ-natural; associator-natural
    ; triangle; pentagon
    )

open import ParaForge.Para.Actegory.Bicategory public
  using (composition; ParaActegory)

open import ParaForge.Para.Actegory.Instance.Sets public
  using
    ( Sets-Monoidal; Sets-Actegory; Sets-Symmetric
    ; Sets-ParameterComonoid; Sets-ParameterCocommutative
    ; toConcrete; fromConcrete
    ; toConcreteCell; fromConcreteCell
    )

open import ParaForge.Actegory.Strong.Instance.Sets public
  using
    ( FoldingFunctor; FoldingStrength; FoldingStrongEndofunctor
    ; UnfoldingFunctor; UnfoldingStrength; UnfoldingStrongEndofunctor
    )

open import ParaForge.Para.Actegory.Instance.Monoidal public
  using
    ( SelfActionPara; MonoidalPara
    ; toMonoidal; fromMonoidal
    ; toMonoidal-run; fromMonoidal-run
    ; toMonoidalCell; fromMonoidalCell
    ; to-from-cell-map; from-to-cell-map
    ; identity-agrees; composition-agrees
    ; identity-cell-agrees
    ; vertical-composition-agrees; horizontal-composition-agrees
    )
