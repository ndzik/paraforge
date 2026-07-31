{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Bicategory where

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

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Hom using (Hom)
import ParaForge.Para.Actegory.Laws as Laws

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

composition :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M}
    (𝒜 : Actegory V 𝒞)
    (A B D : Category.Obj 𝒞) →
  Functor
    (Product (Hom 𝒜 B D) (Hom 𝒜 A B))
    (Hom 𝒜 A D)
composition 𝒜 A B D = record
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

-- Para for an arbitrary action of a monoidal parameter category M on C.
--
--   1-cells: Set (oₘ ⊔ ℓ𝒞)
--   2-cells: Set (ℓₘ ⊔ e𝒞)
--   2-cell equality: Set eₘ
--   0-cells: Obj C : Set o𝒞
ParaActegory :
  ∀ {M : Category oₘ ℓₘ eₘ}
    {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
    {V : Monoidal M} →
  Actegory V 𝒞 →
  Bicategory (oₘ ⊔ ℓ𝒞) (ℓₘ ⊔ e𝒞) eₘ o𝒞
ParaActegory {𝒞 = 𝒞} 𝒜 = record
  { enriched = record
      { Obj = Category.Obj 𝒞
      ; hom = Hom 𝒜
      ; id = λ {A} →
          const (idₚ {𝒜 = 𝒜} {A = A})
      ; ⊚ = λ {A} {B} {C = D} → composition 𝒜 A B D
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
