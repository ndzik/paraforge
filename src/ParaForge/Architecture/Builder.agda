{-# OPTIONS --safe --without-K #-}

module ParaForge.Architecture.Builder where

open import Level using (Level)
open import Data.List.Base using ([]; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Architecture.Core

module Build
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ) where

  private
    module S = Signature Σ
    module D = DataflowSignature D

    variable
      A B C E : S.InterfaceCode
      Γ Δ Π : Context Σ

  Module : Context Σ → S.InterfaceCode → S.InterfaceCode → Set _
  Module = Network D

  identityModule : Module [] A A
  identityModule = network [] (idC D) identity

  infixl 6 _>>>_

  -- Ordinary composition keeps parameter declarations independent.
  _>>>_ : Module Γ A B → Module Δ B C → Module (Δ ++ Γ) A C
  first >>> later = network
    (Occurrences later ++ Occurrences first)
    (body first >>>C body later)
    (binding later ⊗w binding first)

  -- Modules in one lexical parameter scope compose without duplicating their
  -- external declarations. The explicit comonoid capability supplies the
  -- contraction/deletion needed by each body's binding.
  composeShared :
    AllShareable Σ Π →
    Module Π A B → Module Π B C → Module Π A C
  composeShared evidence first later = network
    (Occurrences later ++ Occurrences first)
    (body first >>>C body later)
    ((binding later ⊗w binding first) ∘w
      copyParameters Σ evidence)

  infixl 7 _***_

  _***_ :
    Module Γ A B → Module Δ C E →
    Module (Δ ++ Γ)
      (D.tensorInterface A C)
      (D.tensorInterface B E)
  left *** right = network
    (Occurrences right ++ Occurrences left)
    (body left ***C body right)
    (binding right ⊗w binding left)

  -- Fan-out is computation-side copying. Parameter contexts remain governed
  -- by the two branch bindings.
  fork :
    Module Γ A B → Module Δ A C →
    Module (Δ ++ Γ) A (D.tensorInterface B C)
  fork left right = network
    (Occurrences right ++ Occurrences left)
    (restrictC rightUnit
      (wireC copyData >>>C
        (body left ***C body right)))
    (binding right ⊗w binding left)

  -- Residual is a derived graph combinator. The merger is parameter-free and
  -- the branch's external binding is reused unchanged.
  residualWith :
    CartesianArch D []
      (D.tensorInterface A A) A →
    Module Π A A → Module Π A A
  residualWith merge branch = network
    (Occurrences branch)
    (restrictC rightUnit
      (wireC copyData >>>C
        ((body branch ***C idC D) >>>C merge)))
    (binding branch)

  repeatContext : ℕ → Context Σ → Context Σ
  repeatContext zero Γ = []
  repeatContext (suc count) Γ = Γ ++ repeatContext count Γ

  repeatIndependent :
    (count : ℕ) → Module Γ A A →
    Module (repeatContext count Γ) A A
  repeatIndependent zero architecture = identityModule
  repeatIndependent (suc count) architecture =
    repeatIndependent count architecture >>> architecture

  sharedContext : ℕ → Context Σ → Context Σ
  sharedContext zero Γ = []
  sharedContext (suc _) Γ = Γ

  repeatShared₁ :
    (additionalCopies : ℕ) →
    AllShareable Σ Γ → Module Γ A A → Module Γ A A
  repeatShared₁ zero evidence architecture = architecture
  repeatShared₁ (suc count) evidence architecture =
    composeShared evidence
      (repeatShared₁ count evidence architecture)
      architecture

  repeatShared :
    (count : ℕ) →
    AllShareable Σ Γ → Module Γ A A →
    Module (sharedContext count Γ) A A
  repeatShared zero evidence architecture = identityModule
  repeatShared (suc count) evidence architecture =
    repeatShared₁ count evidence architecture

open Build public
