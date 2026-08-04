{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Interpretation where

open import Level using (Level)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Core
open import ParaForge.Architecture.Transformation
open import ParaForge.Learning.Architecture.Wiring
open import ParaForge.Learning.Architecture.Parameter
open import ParaForge.Learning.Architecture.Model

module InterpretArchitecture
  {i p g pv pf v f : Level}
  {Σ : Signature i p g}
  {D : DataflowSignature Σ}
  (M : ArchitectureLearningModel Σ D pv pf v f) where

  private
    module S = Signature Σ
    module M = ArchitectureLearningModel M
    module Data = InterpretDataWiring M.dataflowLearning
    module Parameter = InterpretParameterWiring M.parameterLearning

    variable
      A B C : S.InterfaceCode
      Γ Δ : Context Σ

  interpretCore :
    CoreArch Σ Γ A B →
    ArchitectureLearner Σ
      (interpretInterface M.dataflowLearning)
      (interpretParameter M.parameterLearning)
      Γ A B
  interpretCore idA = identityArchitecture
  interpretCore (primA operation) = M.primitiveLearning operation
  interpretCore (first >>>A later) =
    sequentialArchitecture
      (interpretCore first)
      (interpretCore later)
  interpretCore (restrictA wire architecture) =
    restrictArchitecture
      (Parameter.interpretParamWire wire)
      (interpretCore architecture)

  interpretCartesian :
    CartesianArch D Γ A B →
    ArchitectureLearner Σ
      (interpretInterface M.dataflowLearning)
      (interpretParameter M.parameterLearning)
      Γ A B
  interpretCartesian (core architecture) = interpretCore architecture
  interpretCartesian (first >>>C later) =
    sequentialArchitecture
      (interpretCartesian first)
      (interpretCartesian later)
  interpretCartesian (left ***C right) =
    parallelArchitecture M.dataflowLearning
      (interpretCartesian left)
      (interpretCartesian right)
  interpretCartesian (wireC wire) =
    parameterFreeArchitecture (Data.interpretDataWire wire)
  interpretCartesian (restrictC wire architecture) =
    restrictArchitecture
      (Parameter.interpretParamWire wire)
      (interpretCartesian architecture)

  interpretNetwork :
    Network D Γ A B →
    ArchitectureLearner Σ
      (interpretInterface M.dataflowLearning)
      (interpretParameter M.parameterLearning)
      Γ A B
  interpretNetwork architecture = restrictArchitecture
    (Parameter.interpretParamWire (binding architecture))
    (interpretCartesian (body architecture))

  -- A learning interpretation of an architecture cell requires backward
  -- parameter transport, not merely its forward G.1 map. ParameterLearningModel
  -- supplies that transport for every wire admitted by the signature.
  interpretCellParameters :
    ∀ {Γ Δ A B}
      {F : CartesianArch D Γ A B}
      {G : CartesianArch D Δ A B} →
    ArchitectureCell D F G →
    ParameterLens Σ
      (interpretParameter M.parameterLearning) Δ Γ
  interpretCellParameters idCell = identityParameterLens
  interpretCellParameters (restrictionCell wire) =
    Parameter.interpretParamWire wire
  interpretCellParameters (later ∘vCell earlier) =
    composeParameterLens
      (interpretCellParameters earlier)
      (interpretCellParameters later)
  interpretCellParameters (later ∘hCell first) =
    tensorParameterLens
      (interpretCellParameters later)
      (interpretCellParameters first)
