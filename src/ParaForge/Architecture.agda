{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture where

-- Provisional Milestone 7 facade. It remains separate from ParaForge until the
-- embedded builder has seen further architecture case studies.
open import ParaForge.Architecture.Signature public
open import ParaForge.Architecture.Wiring public
open import ParaForge.Architecture.Core public
open import ParaForge.Architecture.Transformation public
open import ParaForge.Architecture.Interpretation public

import ParaForge.Architecture.Builder as GenericBuilder
module Generic = GenericBuilder

open import ParaForge.Architecture.Builder.Neural public

open import ParaForge.Architecture.Model public
  using
    ( Interface; one; vector; tokens; _⊗ᵢ_
    ; Parameter; denseP; layerNormP; attentionP; feedForwardP
    ; ParamCtx
    )

open import ParaForge.Architecture.Instance.Sets public
  using
    ( SetsModel; SetsArchitecture; Value; ParameterValue
    ; toPara
    ; toGenericPara; genericRestrictionCell
    )
  renaming (restrictionCell to setsRestrictionCell)

open import ParaForge.Architecture.Instance.Symbolic public
  using
    ( SymbolicModel; SymbolicArchitecture; Node
    ; nodes; depth
    ; externalParameterCount; rawParameterOccurrenceCount
    ; sharingClasses
    )
