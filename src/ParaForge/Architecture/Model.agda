{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Model where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)

-- Phase 27 deliberately starts with codes interpreted by multiple models,
-- rather than an initial architecture AST.
data Interface : Set where
  one    : Interface
  vector : ℕ → Interface
  tokens : (sequenceLength modelWidth : ℕ) → Interface
  _⊗ᵢ_   : Interface → Interface → Interface

infixr 7 _⊗ᵢ_

data Parameter : Set where
  denseP       : (inputWidth outputWidth : ℕ) → Parameter
  layerNormP   : (modelWidth : ℕ) → Parameter
  attentionP   : (heads modelWidth : ℕ) → Parameter
  feedForwardP : (modelWidth hiddenWidth : ℕ) → Parameter

ParamCtx : Set
ParamCtx = List Parameter

private
  variable
    A B C D : Interface
    P Q : Parameter
    Γ Δ Θ Occurrences₁ Occurrences₂ : ParamCtx
    F : Parameter → Set

-- A small common signature is enough to discover the operations required by
-- an MLP and a pre-normalized Transformer encoder block.
data Primitive : ParamCtx → Interface → Interface → Set where
  dense : ∀ inputWidth outputWidth →
    Primitive
      (denseP inputWidth outputWidth ∷ [])
      (vector inputWidth)
      (vector outputWidth)

  relu : ∀ width → Primitive [] (vector width) (vector width)

  softmax : ∀ width → Primitive [] (vector width) (vector width)

  layerNorm : ∀ sequenceLength modelWidth →
    Primitive
      (layerNormP modelWidth ∷ [])
      (tokens sequenceLength modelWidth)
      (tokens sequenceLength modelWidth)

  selfAttention : ∀ sequenceLength modelWidth heads →
    Primitive
      (attentionP heads modelWidth ∷ [])
      (tokens sequenceLength modelWidth)
      (tokens sequenceLength modelWidth)

  feedForward : ∀ sequenceLength modelWidth hiddenWidth →
    Primitive
      (feedForwardP modelWidth hiddenWidth ∷ [])
      (tokens sequenceLength modelWidth)
      (tokens sequenceLength modelWidth)

  addTokens : ∀ sequenceLength modelWidth →
    Primitive []
      (tokens sequenceLength modelWidth ⊗ᵢ
        tokens sequenceLength modelWidth)
      (tokens sequenceLength modelWidth)

-- Data wiring belongs to the computation side. In particular, copying an
-- activation for a residual branch is not parameter sharing.
data DataWire : Interface → Interface → Set where
  copyData    : DataWire A (A ⊗ᵢ A)
  discardData : DataWire A one
  swapData    : DataWire (A ⊗ᵢ B) (B ⊗ᵢ A)
  associateˡ  : DataWire ((A ⊗ᵢ B) ⊗ᵢ C) (A ⊗ᵢ (B ⊗ᵢ C))
  associateʳ  : DataWire (A ⊗ᵢ (B ⊗ᵢ C)) ((A ⊗ᵢ B) ⊗ᵢ C)

-- A slot is a typed de Bruijn reference into an external parameter context.
data Slot (P : Parameter) : ParamCtx → Set where
  here  : Slot P (P ∷ Γ)
  there : Slot P Γ → Slot P (Q ∷ Γ)

-- ParamWire Δ Γ points from the external/new context Δ to the untied
-- occurrence context Γ. This is the normalized syntactic form of the G.1
-- target-to-source parameter map.
data ParamWire (Δ : ParamCtx) : ParamCtx → Set where
  empty  : ParamWire Δ []
  select : Slot P Δ → ParamWire Δ Γ → ParamWire Δ (P ∷ Γ)

mapWire :
  (∀ {P} → Slot P Δ → Slot P Θ) →
  ParamWire Δ Γ → ParamWire Θ Γ
mapWire embedding empty = empty
mapWire embedding (select slot rest) =
  select (embedding slot) (mapWire embedding rest)

lookupWire : Slot P Δ → ParamWire Θ Δ → Slot P Θ
lookupWire here (select slot _) = slot
lookupWire (there wanted) (select _ rest) = lookupWire wanted rest

composeWire : ParamWire Θ Δ → ParamWire Δ Γ → ParamWire Θ Γ
composeWire outer empty = empty
composeWire outer (select slot rest) =
  select (lookupWire slot outer) (composeWire outer rest)

appendWire : ParamWire Δ Γ → ParamWire Δ Θ → ParamWire Δ (Γ ++ Θ)
appendWire empty right = right
appendWire (select slot left) right =
  select slot (appendWire left right)

idWire : ParamWire Γ Γ
idWire {[]} = empty
idWire {P ∷ Γ} = select here (mapWire there idWire)

-- Lists normalize the empty context on the left, but not on the right for an
-- unknown Γ. This explicit wire is the syntactic right-unitor normalization
-- required after composing a parameter-free operation before Γ.
rightUnitWire : ParamWire Γ (Γ ++ [])
rightUnitWire {[]} = empty
rightUnitWire {P ∷ Γ} =
  select here (mapWire there rightUnitWire)

injectLeft : Slot P Δ → Slot P (Δ ++ Γ)
injectLeft here = here
injectLeft (there slot) = there (injectLeft slot)

injectRight : (Δ : ParamCtx) → Slot P Γ → Slot P (Δ ++ Γ)
injectRight [] slot = slot
injectRight (_ ∷ Δ) slot = there (injectRight Δ slot)

-- Combining architectures retains the later-before-earlier parameter order.
mergeWire :
  ParamWire Δ Occurrences₂ →
  ParamWire Γ Occurrences₁ →
  ParamWire (Δ ++ Γ) (Occurrences₂ ++ Occurrences₁)
mergeWire later earlier =
  appendWire
    (mapWire injectLeft later)
    (mapWire (injectRight _) earlier)

duplicateWire : ParamWire Γ (Γ ++ Γ)
duplicateWire = appendWire idWire idWire

-- Environments give ParamWire an executable, interpretation-independent
-- action. Unused external slots implement deletion; repeated selections
-- implement sharing.
data Env (F : Parameter → Set) : ParamCtx → Set where
  ε    : Env F []
  _∷ₑ_ : F P → Env F Γ → Env F (P ∷ Γ)

infixr 5 _∷ₑ_

lookupEnv : Slot P Γ → Env F Γ → F P
lookupEnv here (value ∷ₑ _) = value
lookupEnv (there slot) (_ ∷ₑ rest) = lookupEnv slot rest

applyWire : ParamWire Δ Γ → Env F Δ → Env F Γ
applyWire empty environment = ε
applyWire (select slot wire) environment =
  lookupEnv slot environment ∷ₑ applyWire wire environment

splitEnv : (Δ : ParamCtx) → Env F (Δ ++ Γ) → Env F Δ × Env F Γ
splitEnv [] environment = ε , environment
splitEnv (_ ∷ Δ) (value ∷ₑ environment) with splitEnv Δ environment
... | earlier , later = (value ∷ₑ earlier) , later

-- Tagless-final models validate the operation set before Phase 28 commits to
-- an initial CoreArch representation.
record Model : Set₁ where
  field
    Architecture : ParamCtx → Interface → Interface → Set

    identity : Architecture [] A A

    interpretPrimitive : Primitive Γ A B → Architecture Γ A B

    sequential :
      Architecture Γ A B →
      Architecture Δ B C →
      Architecture (Δ ++ Γ) A C

    parallel :
      Architecture Γ A B →
      Architecture Δ C D →
      Architecture (Δ ++ Γ) (A ⊗ᵢ C) (B ⊗ᵢ D)

    dataWire : DataWire A B → Architecture [] A B

    restrict :
      ParamWire Δ Γ →
      Architecture Γ A B →
      Architecture Δ A B
