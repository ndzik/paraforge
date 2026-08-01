{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Signature where

open import Level using (Level; suc; _⊔_)
open import Data.List.Base using (List)

private
  variable
    i p g : Level

-- A signature contains codes only. Models decide what the codes mean.
record Signature
  (i p g : Level) : Set (suc (i ⊔ p ⊔ g)) where
  field
    InterfaceCode : Set i
    ParameterCode : Set p

    PrimitiveCode :
      List ParameterCode →
      InterfaceCode → InterfaceCode → Set g

    -- Arbitrary reparameterizations are declared by the signature rather than
    -- smuggled in as untyped functions.
    ReparameterizationCode :
      List ParameterCode → List ParameterCode → Set g

    -- Structural contraction and weakening require explicit parameter-side
    -- capability. A semantic model must interpret this as a comonoid.
    Shareable : ParameterCode → Set g

open Signature public

Context : Signature i p g → Set p
Context Σ = List (ParameterCode Σ)

-- Parallel/cartesian dataflow is a capability layered over a primitive
-- signature. A sequential model need not provide either operation.
record DataflowSignature
  (Σ : Signature i p g) : Set i where
  field
    unitInterface   : InterfaceCode Σ
    tensorInterface : InterfaceCode Σ → InterfaceCode Σ → InterfaceCode Σ

open DataflowSignature public
