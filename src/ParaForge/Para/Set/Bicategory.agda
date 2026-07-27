{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Set.Bicategory where

-- Packaging of concrete Para(Set) through the enriched bicategory interface
-- provided by agda-categories. Raw operations and coherence proofs remain in
-- Set, Reparameterization, Hom, and Laws.

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization
open import ParaForge.Para.Set.Hom using (Hom)
import ParaForge.Para.Set.Laws as Laws

-- Sequential and horizontal composition form a bifunctor between the hom
-- categories. Its functor laws are horizontal identity and interchange.
composition :
  ∀ {o p : Level} (A B C : Set o) →
  Functor
    (Product (Hom {p = p} B C) (Hom {p = p} A B))
    (Hom {p = p} A C)
composition A B C = record
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

-- Concrete Para(Set), for sets in universe o and parameter types in the fixed
-- universe p. The hom-category levels determine the first three bicategory
-- levels; the collection Set o of 0-cells lives in suc o.
ParaSet :
  (o p : Level) →
  Bicategory (o ⊔ suc p) (o ⊔ p) p (suc o)
ParaSet o p = record
  { enriched = record
      { Obj = Set o
      ; hom = Hom {p = p}
      ; id = λ {A} →
          const (idₚ {o = o} {p = p} {A = A})
      ; ⊚ = λ {A} {B} {C} → composition A B C
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
