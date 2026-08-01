{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Wiring where

open import Level using (Level; _⊔_)
open import Data.List.Base using ([]; _∷_; _++_)

open import ParaForge.Architecture.Signature

private
  variable
    i p g : Level
    Σ : Signature i p g

module DataWiring
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) where
  private
    module D = DataflowSignature D

  private
    variable
      A B C : InterfaceCode Σ

  -- Computation-side structural wiring is independent of parameter wiring.
  data DataWire :
    InterfaceCode Σ → InterfaceCode Σ → Set (i ⊔ p ⊔ g) where
    copyData : DataWire A (D.tensorInterface A A)
    discardData : DataWire A D.unitInterface
    swapData :
      DataWire
        (D.tensorInterface A B)
        (D.tensorInterface B A)
    associateˡ :
      DataWire
        (D.tensorInterface (D.tensorInterface A B) C)
        (D.tensorInterface A (D.tensorInterface B C))
    associateʳ :
      DataWire
        (D.tensorInterface A (D.tensorInterface B C))
        (D.tensorInterface (D.tensorInterface A B) C)

open DataWiring public

module ParameterWiring
  {i p g : Level}
  (Σ : Signature i p g) where
  private
    module S = Signature Σ

  private
    variable
      P Q : S.ParameterCode
      Γ Δ Θ Λ : Context Σ

  data AllShareable : Context Σ → Set (p ⊔ g) where
    shareable[] : AllShareable []
    _∷ₛ_ : S.Shareable P → AllShareable Γ → AllShareable (P ∷ Γ)

  infixr 5 _∷ₛ_

  -- Typed de Bruijn selections are retained as a cartesian elaboration
  -- language. They become a ParamWire only when the whole external context
  -- carries explicit shareability/deletion evidence.
  data Slot (P : S.ParameterCode) : Context Σ → Set p where
    here  : Slot P (P ∷ Γ)
    there : Slot P Γ → Slot P (Q ∷ Γ)

  data Selection (Δ : Context Σ) : Context Σ → Set p where
    select[] : Selection Δ []
    select : Slot P Δ → Selection Δ Γ → Selection Δ (P ∷ Γ)

  mapSelection :
    (∀ {P} → Slot P Δ → Slot P Θ) →
    Selection Δ Γ → Selection Θ Γ
  mapSelection embedding select[] = select[]
  mapSelection embedding (select slot rest) =
    select (embedding slot) (mapSelection embedding rest)

  lookupSelection : Slot P Δ → Selection Θ Δ → Slot P Θ
  lookupSelection here (select slot _) = slot
  lookupSelection (there wanted) (select _ rest) =
    lookupSelection wanted rest

  composeSelection :
    Selection Θ Δ → Selection Δ Γ → Selection Θ Γ
  composeSelection outer select[] = select[]
  composeSelection outer (select slot rest) =
    select
      (lookupSelection slot outer)
      (composeSelection outer rest)

  appendSelection :
    Selection Δ Γ → Selection Δ Θ → Selection Δ (Γ ++ Θ)
  appendSelection select[] right = right
  appendSelection (select slot left) right =
    select slot (appendSelection left right)

  idSelection : Selection Γ Γ
  idSelection {Γ = []} = select[]
  idSelection {Γ = P ∷ Γ} =
    select here (mapSelection there idSelection)

  duplicateSelection : Selection Γ (Γ ++ Γ)
  duplicateSelection = appendSelection idSelection idSelection

  -- ParamWire Δ Γ has the G.1 direction: external/new Δ points back to the
  -- parameter context Γ expected by the architecture being restricted.
  data ParamWire : Context Σ → Context Σ → Set (p ⊔ g) where
    identity : ParamWire Γ Γ

    _∘w_ : ParamWire Δ Γ → ParamWire Θ Δ → ParamWire Θ Γ

    _⊗w_ :
      ParamWire Δ Γ → ParamWire Θ Λ →
      ParamWire (Δ ++ Θ) (Γ ++ Λ)

    generated :
      S.ReparameterizationCode Δ Γ → ParamWire Δ Γ

    cartesian :
      AllShareable Δ → Selection Δ Γ → ParamWire Δ Γ

    rightUnit : ParamWire Γ (Γ ++ [])

  infixr 8 _∘w_
  infixr 9 _⊗w_

  copyParameters : AllShareable Γ → ParamWire Γ (Γ ++ Γ)
  copyParameters evidence = cartesian evidence duplicateSelection

  discardParameters : AllShareable Γ → ParamWire Γ []
  discardParameters evidence = cartesian evidence select[]

open ParameterWiring public
