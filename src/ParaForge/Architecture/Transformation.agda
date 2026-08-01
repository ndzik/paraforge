{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Transformation where

open import Level using (Level; _⊔_)
open import Data.List.Base using (_++_)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core

module CartesianCells
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) where

  private
    module S = Signature Σ

    variable
      A B C : S.InterfaceCode
      Γ Γ′ Δ Δ′ Θ : Context Σ
      F : CartesianArch D Γ A B
      F′ : CartesianArch D Γ′ A B
      G : CartesianArch D Δ B C
      G′ : CartesianArch D Δ′ B C
      H : CartesianArch D Θ A B

  -- Reparameterizations are explicit syntax. Coherence witnesses remain in
  -- interpretation rather than becoming surface constructors.
  data ArchitectureCell :
    {Γ Δ : Context Σ} →
    CartesianArch D Γ A B →
    CartesianArch D Δ A B →
    Set (i ⊔ p ⊔ g) where

    idCell : ArchitectureCell F F

    restrictionCell :
      (wire : ParamWire Σ Δ Γ) →
      ArchitectureCell F (restrictC wire F)

    _∘vCell_ :
      ArchitectureCell F′ H →
      ArchitectureCell F F′ →
      ArchitectureCell F H

    _∘hCell_ :
      ArchitectureCell G G′ →
      ArchitectureCell F F′ →
      ArchitectureCell
        (F >>>C G)
        (F′ >>>C G′)

  infixr 7 _∘vCell_
  infixr 8 _∘hCell_

open CartesianCells public
