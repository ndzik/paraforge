{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Core where

open import Level using (Level; _⊔_)
open import Data.List.Base using ([]; _++_)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring

module Sequential
  {i p g : Level}
  (Σ : Signature i p g) where

  private
    module S = Signature Σ

  private
    variable
      A B C : S.InterfaceCode
      Γ Δ : Context Σ

  -- The initial sequential syntax has no cartesian computation assumptions.
  -- Its only parameter operation is an explicit G.1-oriented restriction.
  data CoreArch :
    Context Σ → S.InterfaceCode → S.InterfaceCode →
    Set (i ⊔ p ⊔ g) where

    idA : CoreArch [] A A

    primA : S.PrimitiveCode Γ A B → CoreArch Γ A B

    _>>>A_ :
      CoreArch Γ A B →
      CoreArch Δ B C →
      CoreArch (Δ ++ Γ) A C

    restrictA :
      ParamWire Σ Δ Γ →
      CoreArch Γ A B →
      CoreArch Δ A B

  infixl 7 _>>>A_

open Sequential public

module Cartesian
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) where

  private
    module S = Signature Σ
    module D = DataflowSignature D

  private
    variable
      A B C E : S.InterfaceCode
      Γ Δ : Context Σ

  -- CartesianArch is a capability extension, not an assumption added to
  -- CoreArch. Sequential terms embed without acquiring new equations.
  data CartesianArch :
    Context Σ → S.InterfaceCode → S.InterfaceCode →
    Set (i ⊔ p ⊔ g) where

    core : CoreArch Σ Γ A B → CartesianArch Γ A B

    _>>>C_ :
      CartesianArch Γ A B →
      CartesianArch Δ B C →
      CartesianArch (Δ ++ Γ) A C

    _***C_ :
      CartesianArch Γ A B →
      CartesianArch Δ C E →
      CartesianArch (Δ ++ Γ)
        (D.tensorInterface A C)
        (D.tensorInterface B E)

    wireC : DataWire D A B → CartesianArch [] A B

    restrictC :
      ParamWire Σ Δ Γ →
      CartesianArch Γ A B →
      CartesianArch Δ A B

  infixl 7 _>>>C_
  infixl 8 _***C_

  idC : CartesianArch [] A A
  idC = core idA

  primC : S.PrimitiveCode Γ A B → CartesianArch Γ A B
  primC operation = core (primA operation)

  -- A network separates untied primitive occurrences from the externally
  -- visible parameter context governing them.
  record Network
    (Π : Context Σ) (A B : S.InterfaceCode) :
    Set (i ⊔ p ⊔ g) where
    constructor network
    field
      Occurrences : Context Σ
      body : CartesianArch Occurrences A B
      binding : ParamWire Σ Π Occurrences

  open Network public

open Cartesian public
