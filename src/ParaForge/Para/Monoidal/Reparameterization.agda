{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal.Reparameterization where

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning

open import ParaForge.Para.Monoidal

private
  variable
    o ℓ e : Level

-- A G.1 cell F ⇒ G carries a parameter morphism in the opposite direction,
-- from G's parameters to F's parameters. Preservation is an equation in the
-- ambient category's hom-setoid, not propositional equality of morphisms.
module _ {C : Category o ℓ e} (M : Monoidal C) where

  private
    module C = Category C

  open C using (Obj; id; _∘_)
  open Monoidal M using
    (_⊗₁_; module associator)

  private
    variable
      A B : Obj

  record Reparameterization (F G : Para M A B) : Set (ℓ ⊔ e) where
    constructor mkReparameterization
    field
      mapParameters : Parameters G C.⇒ Parameters F
      preserves-run : run G C.≈ run F ∘ (mapParameters ⊗₁ id)

open Reparameterization public

-- M is implicit for cell operations because their Reparameterization operands
-- determine it. This preserves the intended infix notation outside this file.
module _ {C : Category o ℓ e} {M : Monoidal C} where

  private
    module C = Category C

  open C using (Obj; id; _∘_)
  open Monoidal M using
    (_⊗₁_; module associator)

  private
    variable
      A B D : Obj
      F G H I : Para M A B

  -- Cells are observed only through their parameter morphisms. Preservation
  -- proofs remain required construction data but are deliberately not compared.
  infix 4 _≈_

  _≈_ : Reparameterization M F G → Reparameterization M F G → Set e
  α ≈ β = mapParameters α C.≈ mapParameters β

  ≈-refl : (α : Reparameterization M F G) → α ≈ α
  ≈-refl α = C.Equiv.refl

  ≈-sym : {α β : Reparameterization M F G} → α ≈ β → β ≈ α
  ≈-sym = C.Equiv.sym

  ≈-trans : {α β γ : Reparameterization M F G} →
    α ≈ β → β ≈ γ → α ≈ γ
  ≈-trans = C.Equiv.trans

  reparameterizationSetoid :
    (F G : Para M A B) → Setoid (ℓ ⊔ e) e
  reparameterizationSetoid F G = record
    { Carrier = Reparameterization M F G
    ; _≈_ = _≈_
    ; isEquivalence = record
        { refl = C.Equiv.refl
        ; sym = C.Equiv.sym
        ; trans = C.Equiv.trans
        }
    }

  identityPreserves : run F C.≈ run F ∘ (id ⊗₁ id)
  identityPreserves {F = F} = begin
    run F                    ≈˘⟨ C.identityʳ ⟩
    run F ∘ id               ≈˘⟨ C.Equiv.refl ⟩∘⟨ Monoidal.⊗.identity M ⟩
    run F ∘ (id ⊗₁ id)      ∎
    where
      open C.HomReasoning

  id₂ : Reparameterization M F F
  id₂ = mkReparameterization id identityPreserves

  verticalPreserves :
    (β : Reparameterization M G H) →
    (α : Reparameterization M F G) →
    run H C.≈ run F ∘ ((mapParameters α ∘ mapParameters β) ⊗₁ id)
  verticalPreserves β α =
    preserves-run β
      ○ (preserves-run α ⟩∘⟨refl)
      ○ C.assoc
      ○ (refl⟩∘⟨ C.Equiv.sym
          (MonoidalReasoning.⊗-distrib-over-∘ M))
      ○ (refl⟩∘⟨ (refl⟩⊗⟨ C.identity²))
    where
      open C.HomReasoning
      open MonoidalReasoning M using (refl⟩⊗⟨_)

  infixr 7 _∘ᵥ_

  _∘ᵥ_ :
    Reparameterization M G H →
    Reparameterization M F G →
    Reparameterization M F H
  β ∘ᵥ α = mkReparameterization
    (mapParameters α ∘ mapParameters β)
    (verticalPreserves β α)

  ∘ᵥ-resp-≈ :
    {α α′ : Reparameterization M F G} →
    {β β′ : Reparameterization M G H} →
    β ≈ β′ → α ≈ α′ →
    (β ∘ᵥ α) ≈ (β′ ∘ᵥ α′)
  ∘ᵥ-resp-≈ β≈β′ α≈α′ = C.∘-resp-≈ α≈α′ β≈β′

  ∘ᵥ-identityˡ : (α : Reparameterization M F G) →
    (id₂ {F = G} ∘ᵥ α) ≈ α
  ∘ᵥ-identityˡ α = C.identityʳ

  ∘ᵥ-identityʳ : (α : Reparameterization M F G) →
    (α ∘ᵥ id₂ {F = F}) ≈ α
  ∘ᵥ-identityʳ α = C.identityˡ

  ∘ᵥ-assoc :
    (γ : Reparameterization M H I) →
    (β : Reparameterization M G H) →
    (α : Reparameterization M F G) →
    ((γ ∘ᵥ β) ∘ᵥ α) ≈ (γ ∘ᵥ (β ∘ᵥ α))
  ∘ᵥ-assoc γ β α = C.sym-assoc

  horizontalPreserves :
    ∀ {A B D : Obj}
      {F F′ : Para M A B}
      {G G′ : Para M B D} →
    (β : Reparameterization M G G′) →
    (α : Reparameterization M F F′) →
    run (G′ ∘ₚ F′) C.≈
      run (G ∘ₚ F) ∘
        ((mapParameters β ⊗₁ mapParameters α) ⊗₁ id)
  horizontalPreserves
    {F = F} {F′ = F′} {G = G} {G′ = G′} β α = begin
    run (G′ ∘ₚ F′)
      ≈⟨ C.∘-resp-≈ˡ (preserves-run β) ⟩
    (run G ∘ (mapParameters β ⊗₁ id)) ∘
      ((id ⊗₁ run F′) ∘ associator.from)
      ≈⟨ C.assoc ⟩
    run G ∘ ((mapParameters β ⊗₁ id) ∘
      ((id ⊗₁ run F′) ∘ associator.from))
      ≈⟨ C.∘-resp-≈ʳ C.sym-assoc ⟩
    run G ∘ (((mapParameters β ⊗₁ id) ∘
      (id ⊗₁ run F′)) ∘ associator.from)
      ≈⟨ C.∘-resp-≈ʳ
          (C.∘-resp-≈ˡ (C.Equiv.sym serialize₁₂)) ⟩
    run G ∘ ((mapParameters β ⊗₁ run F′) ∘ associator.from)
      ≈⟨ C.∘-resp-≈ʳ
          (C.∘-resp-≈ˡ (⊗-resp-≈ʳ (preserves-run α))) ⟩
    run G ∘ ((mapParameters β ⊗₁
      (run F ∘ (mapParameters α ⊗₁ id))) ∘ associator.from)
      ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ˡ split₂ʳ) ⟩
    run G ∘ (((mapParameters β ⊗₁ run F) ∘
      (id ⊗₁ (mapParameters α ⊗₁ id))) ∘ associator.from)
      ≈⟨ C.∘-resp-≈ʳ C.assoc ⟩
    run G ∘ ((mapParameters β ⊗₁ run F) ∘
      ((id ⊗₁ (mapParameters α ⊗₁ id)) ∘ associator.from))
      ≈⟨ C.∘-resp-≈ʳ
          (C.∘-resp-≈ˡ serialize₂₁) ⟩
    run G ∘ (((id ⊗₁ run F) ∘
      (mapParameters β ⊗₁ id)) ∘
      ((id ⊗₁ (mapParameters α ⊗₁ id)) ∘ associator.from))
      ≈⟨ C.∘-resp-≈ʳ C.assoc ⟩
    run G ∘ ((id ⊗₁ run F) ∘
      ((mapParameters β ⊗₁ id) ∘
      ((id ⊗₁ (mapParameters α ⊗₁ id)) ∘ associator.from)))
      ≈⟨ C.∘-resp-≈ʳ
          (C.∘-resp-≈ʳ merge-parameter-maps) ⟩
    run G ∘ ((id ⊗₁ run F) ∘
      ((mapParameters β ⊗₁ (mapParameters α ⊗₁ id)) ∘
      associator.from))
      ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
          (C.Equiv.sym (Monoidal.assoc-commute-from M))) ⟩
    run G ∘ ((id ⊗₁ run F) ∘
      (associator.from ∘
      ((mapParameters β ⊗₁ mapParameters α) ⊗₁ id)))
      ≈⟨ C.∘-resp-≈ʳ C.sym-assoc ⟩
    run G ∘ (((id ⊗₁ run F) ∘ associator.from) ∘
      ((mapParameters β ⊗₁ mapParameters α) ⊗₁ id))
      ≈⟨ C.sym-assoc ⟩
    run (G ∘ₚ F) ∘
      ((mapParameters β ⊗₁ mapParameters α) ⊗₁ id)
      ∎
    where
      open C.HomReasoning
      open MonoidalReasoning M using
        (⊗-resp-≈ʳ; serialize₁₂; serialize₂₁; split₂ʳ)

      merge-parameter-maps =
        C.sym-assoc ○
        C.∘-resp-≈ˡ (C.Equiv.sym serialize₁₂)

  infixr 11 _∘ₕ_

  _∘ₕ_ :
    ∀ {A B D : Obj}
      {F F′ : Para M A B}
      {G G′ : Para M B D} →
    Reparameterization M G G′ →
    Reparameterization M F F′ →
    Reparameterization M (G ∘ₚ F) (G′ ∘ₚ F′)
  β ∘ₕ α = mkReparameterization
    (mapParameters β ⊗₁ mapParameters α)
    (horizontalPreserves β α)

  ∘ₕ-resp-≈ :
    ∀ {A B D : Obj}
      {F F′ : Para M A B}
      {G G′ : Para M B D}
      {α α′ : Reparameterization M F F′}
      {β β′ : Reparameterization M G G′} →
    β ≈ β′ → α ≈ α′ →
    (β ∘ₕ α) ≈ (β′ ∘ₕ α′)
  ∘ₕ-resp-≈ = MonoidalReasoning.⊗-resp-≈ M

  ∘ₕ-identity :
    ∀ {A B D : Obj}
      {F : Para M A B}
      {G : Para M B D} →
    (id₂ {F = G} ∘ₕ id₂ {F = F}) ≈ id₂ {F = G ∘ₚ F}
  ∘ₕ-identity = Monoidal.⊗.identity M

  -- Functoriality of tensor is precisely the interchange law for the
  -- target-to-source parameter morphisms.
  interchange :
    ∀ {A B D : Obj}
      {F₀ F₁ F₂ : Para M A B}
      {G₀ G₁ G₂ : Para M B D} →
    (β₁ : Reparameterization M G₀ G₁) →
    (β₂ : Reparameterization M G₁ G₂) →
    (α₁ : Reparameterization M F₀ F₁) →
    (α₂ : Reparameterization M F₁ F₂) →
    ((β₂ ∘ᵥ β₁) ∘ₕ (α₂ ∘ᵥ α₁)) ≈
      ((β₂ ∘ₕ α₂) ∘ᵥ (β₁ ∘ₕ α₁))
  interchange β₁ β₂ α₁ α₂ =
    MonoidalReasoning.⊗-distrib-over-∘ M
