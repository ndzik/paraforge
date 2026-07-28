{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal.Hom where

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Para.Monoidal
open import ParaForge.Para.Monoidal.Reparameterization

private
  variable
    o ℓ e : Level

-- For fixed interfaces A and B, generic parameterized maps are objects and
-- G.1-oriented reparameterizations are morphisms. The three category levels
-- respectively account for raw Para records, proof-carrying cells, and the
-- ambient category's morphism equality.
Hom :
  ∀ {C : Category o ℓ e} (M : Monoidal C) →
  (A B : Category.Obj C) →
  Category (o ⊔ ℓ) (ℓ ⊔ e) e
Hom {C = C} M A B = record
  { Obj = Para M A B
  ; _⇒_ = Reparameterization M
  ; _≈_ = _≈_
  ; id = id₂
  ; _∘_ = _∘ᵥ_
  ; assoc = λ {f = α} {g = β} {h = γ} →
      ∘ᵥ-assoc γ β α
  ; sym-assoc = Category.assoc C
  ; identityˡ = λ {f = α} →
      ∘ᵥ-identityˡ α
  ; identityʳ = λ {f = α} →
      ∘ᵥ-identityʳ α
  ; identity² = λ {A = F} →
      ∘ᵥ-identityˡ (id₂ {F = F})
  ; equiv = λ {A = F} {B = G} →
      Setoid.isEquivalence (reparameterizationSetoid F G)
  ; ∘-resp-≈ = λ {f = β} {h = β′} {g = α} {i = α′} →
      ∘ᵥ-resp-≈
        {α = α} {α′ = α′} {β = β} {β′ = β′}
  }
