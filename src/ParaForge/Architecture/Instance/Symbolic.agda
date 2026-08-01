{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Instance.Symbolic where

open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import ParaForge.Architecture.Model

private
  variable
    A B C D : Interface
    P : Parameter
    Γ Δ : ParamCtx

-- Symbolic nodes intentionally stop at architecture-level operations. For
-- example, attention is one node rather than an uncommitted tensor program.
data Node : Set where
  denseNode       : (inputWidth outputWidth : ℕ) → Node
  reluNode        : (width : ℕ) → Node
  softmaxNode     : (width : ℕ) → Node
  layerNormNode   : (sequenceLength modelWidth : ℕ) → Node
  attentionNode   : (sequenceLength modelWidth heads : ℕ) → Node
  feedForwardNode : (sequenceLength modelWidth hiddenWidth : ℕ) → Node
  addTokensNode   : (sequenceLength modelWidth : ℕ) → Node
  copyDataNode discardDataNode swapDataNode : Node
  associateˡNode associateʳNode : Node

primitiveNode : Primitive Γ A B → Node
primitiveNode (dense inputWidth outputWidth) =
  denseNode inputWidth outputWidth
primitiveNode (relu width) = reluNode width
primitiveNode (softmax width) = softmaxNode width
primitiveNode (layerNorm sequenceLength modelWidth) =
  layerNormNode sequenceLength modelWidth
primitiveNode (selfAttention sequenceLength modelWidth heads) =
  attentionNode sequenceLength modelWidth heads
primitiveNode (feedForward sequenceLength modelWidth hiddenWidth) =
  feedForwardNode sequenceLength modelWidth hiddenWidth
primitiveNode (addTokens sequenceLength modelWidth) =
  addTokensNode sequenceLength modelWidth

dataWireNode : DataWire A B → Node
dataWireNode copyData = copyDataNode
dataWireNode discardData = discardDataNode
dataWireNode swapData = swapDataNode
dataWireNode associateˡ = associateˡNode
dataWireNode associateʳ = associateʳNode

maxNat : ℕ → ℕ → ℕ
maxNat zero right = right
maxNat (suc left) zero = suc left
maxNat (suc left) (suc right) = suc (maxNat left right)

-- This is a semantic graph summary, not the initial CoreArch syntax planned
-- for Phase 28. It records precisely the distinction between external
-- parameters and untied primitive occurrences.
record SymbolicArchitecture
  (Γ : ParamCtx) (A B : Interface) : Set where
  constructor structure
  field
    Occurrences : ParamCtx
    binding     : ParamWire Γ Occurrences
    nodes       : List Node
    depth       : ℕ

open SymbolicArchitecture public

symbolicIdentity : SymbolicArchitecture [] A A
symbolicIdentity = structure [] empty [] zero

symbolicPrimitive : Primitive Γ A B → SymbolicArchitecture Γ A B
symbolicPrimitive operation =
  structure _ idWire (primitiveNode operation ∷ []) (suc zero)

symbolicSequential :
  SymbolicArchitecture Γ A B →
  SymbolicArchitecture Δ B C →
  SymbolicArchitecture (Δ ++ Γ) A C
symbolicSequential first later = structure
  (Occurrences later ++ Occurrences first)
  (mergeWire (binding later) (binding first))
  (nodes first ++ nodes later)
  (depth first + depth later)

symbolicParallel :
  SymbolicArchitecture Γ A B →
  SymbolicArchitecture Δ C D →
  SymbolicArchitecture (Δ ++ Γ) (A ⊗ᵢ C) (B ⊗ᵢ D)
symbolicParallel left right = structure
  (Occurrences right ++ Occurrences left)
  (mergeWire (binding right) (binding left))
  (nodes left ++ nodes right)
  (maxNat (depth left) (depth right))

symbolicDataWire : DataWire A B → SymbolicArchitecture [] A B
symbolicDataWire wire =
  structure [] empty (dataWireNode wire ∷ []) (suc zero)

symbolicRestriction :
  ParamWire Δ Γ →
  SymbolicArchitecture Γ A B →
  SymbolicArchitecture Δ A B
symbolicRestriction wire architecture = structure
  (Occurrences architecture)
  (composeWire wire (binding architecture))
  (nodes architecture)
  (depth architecture)

SymbolicModel : Model
SymbolicModel = record
  { Architecture = SymbolicArchitecture
  ; identity = symbolicIdentity
  ; interpretPrimitive = symbolicPrimitive
  ; sequential = symbolicSequential
  ; parallel = symbolicParallel
  ; dataWire = symbolicDataWire
  ; restrict = symbolicRestriction
  }

slotIndex : Slot P Γ → ℕ
slotIndex here = zero
slotIndex (there slot) = suc (slotIndex slot)

wireClasses : ParamWire Γ Δ → List ℕ
wireClasses empty = []
wireClasses (select slot rest) = slotIndex slot ∷ wireClasses rest

externalParameterCount : SymbolicArchitecture Γ A B → ℕ
externalParameterCount {Γ = Γ} _ = length Γ

rawParameterOccurrenceCount : SymbolicArchitecture Γ A B → ℕ
rawParameterOccurrenceCount architecture = length (Occurrences architecture)

sharingClasses : SymbolicArchitecture Γ A B → List ℕ
sharingClasses architecture = wireClasses (binding architecture)
