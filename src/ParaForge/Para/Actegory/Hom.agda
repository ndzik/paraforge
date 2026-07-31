{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Hom where

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

Hom :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M}
    (𝒜 : Actegory V 𝒞)
    (A B : Category.Obj 𝒞) →
  Category (oₘ ⊔ ℓ𝒞) (ℓₘ ⊔ e𝒞) eₘ
Hom {M = M} 𝒜 A B = record
  { Obj = Para 𝒜 A B
  ; _⇒_ = Reparameterization 𝒜
  ; _≈_ = _≈_
  ; id = id₂
  ; _∘_ = _∘ᵥ_
  ; assoc = λ {f = α} {g = β} {h = γ} →
      ∘ᵥ-assoc γ β α
  ; sym-assoc = Category.assoc M
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
