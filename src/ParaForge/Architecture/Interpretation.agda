{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Interpretation where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic.Base using (⊤)

import ParaForge.Architecture.Model as Final
open import ParaForge.Architecture.Signature
import ParaForge.Architecture.Wiring as ReifiedWire
import ParaForge.Architecture.Core as Reified
import ParaForge.Architecture.Transformation as ReifiedCell
import ParaForge.Architecture.Instance.Sets as Sets
import ParaForge.Para.Set.Reparameterization as ConcreteCells

-- The Phase 27 neural checkpoint becomes the first signature interpreted by
-- the reified core. It declares every parameter code shareable explicitly;
-- future signatures may provide a strictly smaller capability family.
data NoReparameterization
  (Δ Γ : Final.ParamCtx) : Set where

NeuralSignature : Signature 0ℓ 0ℓ 0ℓ
NeuralSignature = record
  { InterfaceCode = Final.Interface
  ; ParameterCode = Final.Parameter
  ; PrimitiveCode = Final.Primitive
  ; ReparameterizationCode = NoReparameterization
  ; Shareable = λ _ → ⊤
  }

NeuralDataflow : DataflowSignature NeuralSignature
NeuralDataflow = record
  { unitInterface = Final.one
  ; tensorInterface = Final._⊗ᵢ_
  }

private
  variable
    A B : Final.Interface
    P : Final.Parameter
    Γ Δ : Final.ParamCtx

eraseSlot :
  ReifiedWire.Slot NeuralSignature P Γ → Final.Slot P Γ
eraseSlot ReifiedWire.here = Final.here
eraseSlot (ReifiedWire.there slot) = Final.there (eraseSlot slot)

eraseSelection :
  ReifiedWire.Selection NeuralSignature Δ Γ → Final.ParamWire Δ Γ
eraseSelection ReifiedWire.select[] = Final.empty
eraseSelection (ReifiedWire.select slot rest) =
  Final.select (eraseSlot slot) (eraseSelection rest)

-- For this cartesian checkpoint every signature-declared generator is empty.
-- Structural wires erase to the Phase 27 selection semantics only after their
-- explicit AllShareable evidence has been checked by the constructor.
eraseParamWire :
  ReifiedWire.ParamWire NeuralSignature Δ Γ → Final.ParamWire Δ Γ
eraseParamWire ReifiedWire.identity = Final.idWire
eraseParamWire (later ReifiedWire.∘w earlier) =
  Final.composeWire (eraseParamWire earlier) (eraseParamWire later)
eraseParamWire (left ReifiedWire.⊗w right) =
  Final.mergeWire (eraseParamWire left) (eraseParamWire right)
eraseParamWire (ReifiedWire.generated ())
eraseParamWire (ReifiedWire.cartesian _ selection) =
  eraseSelection selection
eraseParamWire ReifiedWire.rightUnit = Final.rightUnitWire

eraseDataWire :
  ReifiedWire.DataWire NeuralDataflow A B → Final.DataWire A B
eraseDataWire ReifiedWire.copyData = Final.copyData
eraseDataWire ReifiedWire.discardData = Final.discardData
eraseDataWire ReifiedWire.swapData = Final.swapData
eraseDataWire ReifiedWire.associateˡ = Final.associateˡ
eraseDataWire ReifiedWire.associateʳ = Final.associateʳ

module Interpret (M : Final.Model) where
  private
    module M = Final.Model M

  interpretCore :
    Reified.CoreArch NeuralSignature Γ A B →
    M.Architecture Γ A B
  interpretCore Reified.idA = M.identity
  interpretCore (Reified.primA operation) =
    M.interpretPrimitive operation
  interpretCore (first Reified.>>>A later) =
    M.sequential (interpretCore first) (interpretCore later)
  interpretCore (Reified.restrictA wire architecture) =
    M.restrict (eraseParamWire wire) (interpretCore architecture)

  interpretCartesian :
    Reified.CartesianArch NeuralDataflow Γ A B →
    M.Architecture Γ A B
  interpretCartesian (Reified.core architecture) =
    interpretCore architecture
  interpretCartesian (first Reified.>>>C later) =
    M.sequential
      (interpretCartesian first)
      (interpretCartesian later)
  interpretCartesian (left Reified.***C right) =
    M.parallel
      (interpretCartesian left)
      (interpretCartesian right)
  interpretCartesian (Reified.wireC wire) =
    M.dataWire (eraseDataWire wire)
  interpretCartesian (Reified.restrictC wire architecture) =
    M.restrict
      (eraseParamWire wire)
      (interpretCartesian architecture)

  interpretNetwork :
    Reified.Network NeuralDataflow Γ A B →
    M.Architecture Γ A B
  interpretNetwork architecture =
    M.restrict
      (eraseParamWire (Reified.binding architecture))
      (interpretCartesian (Reified.body architecture))

module InterpretSetsCells where
  module Execute = Interpret Sets.SetsModel

  interpretCell :
    ∀ {A B : Final.Interface} {Γ Δ : Final.ParamCtx}
      {F : Reified.CartesianArch NeuralDataflow Γ A B}
      {G : Reified.CartesianArch NeuralDataflow Δ A B} →
    ReifiedCell.ArchitectureCell NeuralDataflow F G →
    ConcreteCells.Reparameterization
      (Sets.toPara {A = A} {B = B}
        (Execute.interpretCartesian F))
      (Sets.toPara {A = A} {B = B}
        (Execute.interpretCartesian G))
  interpretCell ReifiedCell.idCell = ConcreteCells.id₂
  interpretCell {F = F} (ReifiedCell.restrictionCell wire) =
    Sets.restrictionCell
      (eraseParamWire wire)
      (Execute.interpretCartesian F)
  interpretCell (later ReifiedCell.∘vCell earlier) =
    interpretCell later ConcreteCells.∘ᵥ interpretCell earlier
  interpretCell (later ReifiedCell.∘hCell first) =
    Sets.horizontalCell
      (interpretCell later)
      (interpretCell first)
