{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal.Bicategory where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)

open import ParaForge.Para.Monoidal
open import ParaForge.Para.Monoidal.Reparameterization
open import ParaForge.Para.Monoidal.Hom using (Hom)
import ParaForge.Para.Monoidal.Laws as Laws

private
  variable
    o ℓ e : Level

-- Sequential and horizontal composition form a bifunctor between generic
-- hom-categories. Its laws are tensor identity, interchange, and congruence.
composition :
  ∀ {C : Category o ℓ e} (M : Monoidal C) →
  (A B D : Category.Obj C) →
  Functor
    (Product (Hom M B D) (Hom M A B))
    (Hom M A D)
composition M A B D = record
  { F₀ = λ where
      (G , F) → G ∘ₚ F
  ; F₁ = λ where
      (β , α) → β ∘ₕ α
  ; identity = λ where
      {G , F} → ∘ₕ-identity {F = F} {G = G}
  ; homomorphism = λ where
      {f = (β₁ , α₁)} {g = (β₂ , α₂)} →
        interchange β₁ β₂ α₁ α₂
  ; F-resp-≈ = λ where
      {f = (β , α)} {g = (β′ , α′)} (β≈β′ , α≈α′) →
        ∘ₕ-resp-≈
          {α = α} {α′ = α′} {β = β} {β′ = β′}
          β≈β′ α≈α′
  }

-- Generic Para for the tensor self-action of a monoidal category C.
--
--   1-cells: Set (o ⊔ ℓ)
--   2-cells: Set (ℓ ⊔ e)
--   2-cell equality: Set e
--   0-cells: Obj C : Set o
ParaMonoidal :
  ∀ {C : Category o ℓ e} (M : Monoidal C) →
  Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e o
ParaMonoidal {C = C} M = record
  { enriched = record
      { Obj = Category.Obj C
      ; hom = Hom M
      ; id = λ {A} →
          const (idₚ {M = M} {A = A})
      ; ⊚ = λ {A} {B} {C = D} → composition M A B D
      ; ⊚-assoc = niHelper record
          { η = λ where
              ((H , G) , F) →
                Laws.associator {F = F} {G = G} {H = H}
          ; η⁻¹ = λ where
              ((H , G) , F) →
                Laws.associator⁻¹ {F = F} {G = G} {H = H}
          ; commute = λ where
              ((γ , β) , α) →
                Laws.associator-natural α β γ
          ; iso = λ where
              ((H , G) , F) → record
                { isoˡ = Laws.associator-isoˡ
                    {F = F} {G = G} {H = H}
                ; isoʳ = Laws.associator-isoʳ
                    {F = F} {G = G} {H = H}
                }
          }
      ; unitˡ = niHelper record
          { η = λ where
              (_ , F) → Laws.unitorˡ {F = F}
          ; η⁻¹ = λ where
              (_ , F) → Laws.unitorˡ⁻¹ {F = F}
          ; commute = λ where
              (_ , α) → Laws.unitorˡ-natural α
          ; iso = λ where
              (_ , F) → record
                { isoˡ = Laws.unitorˡ-isoˡ {F = F}
                ; isoʳ = Laws.unitorˡ-isoʳ {F = F}
                }
          }
      ; unitʳ = niHelper record
          { η = λ where
              (F , _) → Laws.unitorʳ {F = F}
          ; η⁻¹ = λ where
              (F , _) → Laws.unitorʳ⁻¹ {F = F}
          ; commute = λ where
              (α , _) → Laws.unitorʳ-natural α
          ; iso = λ where
              (F , _) → record
                { isoˡ = Laws.unitorʳ-isoˡ {F = F}
                ; isoʳ = Laws.unitorʳ-isoʳ {F = F}
                }
          }
      }
  ; triangle = λ {f = F} {g = G} →
      Laws.triangle {F = F} {G = G}
  ; pentagon = λ {f = F} {g = G} {h = H} {i = I} →
      Laws.pentagon {F = F} {G = G} {H = H} {I = I}
  }
