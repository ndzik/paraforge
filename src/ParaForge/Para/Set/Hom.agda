{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Set.Hom where

-- For fixed interfaces A and B, parameterized maps A → B are the objects of
-- a hom-category. Its morphisms are behavior-preserving reparameterizations,
-- composed vertically and compared by pointwise parameter-map equality.

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Category.Core using (Category)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization

Hom :
  ∀ {o p : Level} (A B : Set o) →
  Category (o ⊔ suc p) (o ⊔ p) p
Hom {o} {p} A B = record
  { Obj = Para {o = o} {p = p} A B
  ; _⇒_ = Reparameterization
  ; _≈_ = _≈_
  ; id = id₂
  ; _∘_ = _∘ᵥ_
  ; assoc = λ {f = α} {g = β} {h = γ} →
      ∘ᵥ-assoc γ β α
  ; sym-assoc = λ targetParameter → refl
  ; identityˡ = λ {f = α} →
      ∘ᵥ-identityˡ α
  ; identityʳ = λ {f = α} →
      ∘ᵥ-identityʳ α
  ; identity² = λ {A = F} →
      ∘ᵥ-identityˡ (id₂ {F = F})
  ; equiv = λ {A = F} {B = G} →
      Setoid.isEquivalence (reparameterizationSetoid F G)
  ; ∘-resp-≈ = λ {f = β} {h = β′} {g = α} {i = α′} →
      ∘ᵥ-resp-≈ {α = α} {α′ = α′} {β = β} {β′ = β′}
  }
