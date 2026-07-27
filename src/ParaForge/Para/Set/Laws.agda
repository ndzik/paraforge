{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Set.Laws where

-- Concrete Para(Set) is weak because product parameters are associative and
-- unital only up to canonical reparameterization. This module keeps those
-- cells and their coherence proofs independent from bicategory packaging.

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import ParaForge.Para.Set
open import ParaForge.Para.Set.Reparameterization

-- Left unitor: (idₚ ∘ₚ F) ⇒ F.
unitorˡ-map :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Parameters F →
  Parameters (idₚ {o = o} {p = p} {A = B} ∘ₚ F)
unitorˡ-map parameter = tt , parameter

unitorˡ-preserves :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  ∀ parameter input →
  run F (parameter , input) ≡
  run (idₚ {o = o} {p = p} {A = B} ∘ₚ F)
    (unitorˡ-map {F = F} parameter , input)
unitorˡ-preserves parameter input = refl

unitorˡ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Reparameterization
    (idₚ {o = o} {p = p} {A = B} ∘ₚ F)
    F
unitorˡ {F = F} = mkReparameterization
  (unitorˡ-map {F = F})
  (unitorˡ-preserves {F = F})

unitorˡ⁻¹-map :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Parameters (idₚ {o = o} {p = p} {A = B} ∘ₚ F) →
  Parameters F
unitorˡ⁻¹-map (_ , parameter) = parameter

unitorˡ⁻¹-preserves :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  ∀ parameter input →
  run (idₚ {o = o} {p = p} {A = B} ∘ₚ F)
    (parameter , input) ≡
  run F (unitorˡ⁻¹-map {F = F} parameter , input)
unitorˡ⁻¹-preserves (_ , parameter) input = refl

unitorˡ⁻¹ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Reparameterization
    F
    (idₚ {o = o} {p = p} {A = B} ∘ₚ F)
unitorˡ⁻¹ {F = F} = mkReparameterization
  (unitorˡ⁻¹-map {F = F})
  (unitorˡ⁻¹-preserves {F = F})

-- Right unitor: (F ∘ₚ idₚ) ⇒ F.
unitorʳ-map :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Parameters F →
  Parameters (F ∘ₚ idₚ {o = o} {p = p} {A = A})
unitorʳ-map parameter = parameter , tt

unitorʳ-preserves :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  ∀ parameter input →
  run F (parameter , input) ≡
  run (F ∘ₚ idₚ {o = o} {p = p} {A = A})
    (unitorʳ-map {F = F} parameter , input)
unitorʳ-preserves parameter input = refl

unitorʳ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Reparameterization
    (F ∘ₚ idₚ {o = o} {p = p} {A = A})
    F
unitorʳ {F = F} = mkReparameterization
  (unitorʳ-map {F = F})
  (unitorʳ-preserves {F = F})

unitorʳ⁻¹-map :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Parameters (F ∘ₚ idₚ {o = o} {p = p} {A = A}) →
  Parameters F
unitorʳ⁻¹-map (parameter , _) = parameter

unitorʳ⁻¹-preserves :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  ∀ parameter input →
  run (F ∘ₚ idₚ {o = o} {p = p} {A = A})
    (parameter , input) ≡
  run F (unitorʳ⁻¹-map {F = F} parameter , input)
unitorʳ⁻¹-preserves (parameter , _) input = refl

unitorʳ⁻¹ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  Reparameterization
    F
    (F ∘ₚ idₚ {o = o} {p = p} {A = A})
unitorʳ⁻¹ {F = F} = mkReparameterization
  (unitorʳ⁻¹-map {F = F})
  (unitorʳ⁻¹-preserves {F = F})

-- Associator: ((H ∘ₚ G) ∘ₚ F) ⇒ (H ∘ₚ (G ∘ₚ F)).
associator-map :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  Parameters (H ∘ₚ (G ∘ₚ F)) →
  Parameters ((H ∘ₚ G) ∘ₚ F)
associator-map (h , (g , f)) = (h , g) , f

associator-preserves :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  ∀ parameter input →
  run (H ∘ₚ (G ∘ₚ F)) (parameter , input) ≡
  run ((H ∘ₚ G) ∘ₚ F)
    (associator-map {F = F} {G = G} {H = H} parameter , input)
associator-preserves (h , (g , f)) input = refl

associator :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  Reparameterization
    ((H ∘ₚ G) ∘ₚ F)
    (H ∘ₚ (G ∘ₚ F))
associator {F = F} {G = G} {H = H} = mkReparameterization
  (associator-map {F = F} {G = G} {H = H})
  (associator-preserves {F = F} {G = G} {H = H})

associator⁻¹-map :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  Parameters ((H ∘ₚ G) ∘ₚ F) →
  Parameters (H ∘ₚ (G ∘ₚ F))
associator⁻¹-map ((h , g) , f) = h , (g , f)

associator⁻¹-preserves :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  ∀ parameter input →
  run ((H ∘ₚ G) ∘ₚ F) (parameter , input) ≡
  run (H ∘ₚ (G ∘ₚ F))
    (associator⁻¹-map {F = F} {G = G} {H = H} parameter , input)
associator⁻¹-preserves ((h , g) , f) input = refl

associator⁻¹ :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  Reparameterization
    (H ∘ₚ (G ∘ₚ F))
    ((H ∘ₚ G) ∘ₚ F)
associator⁻¹ {F = F} {G = G} {H = H} = mkReparameterization
  (associator⁻¹-map {F = F} {G = G} {H = H})
  (associator⁻¹-preserves {F = F} {G = G} {H = H})

-- The canonical cells are invertible under pointwise 2-cell equality.
unitorˡ-isoˡ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  (unitorˡ⁻¹ {F = F} ∘ᵥ unitorˡ {F = F}) ≈
  id₂ {F = idₚ {o = o} {p = p} {A = B} ∘ₚ F}
unitorˡ-isoˡ targetParameter = refl

unitorˡ-isoʳ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  (unitorˡ {F = F} ∘ᵥ unitorˡ⁻¹ {F = F}) ≈ id₂ {F = F}
unitorˡ-isoʳ targetParameter = refl

unitorʳ-isoˡ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  (unitorʳ⁻¹ {F = F} ∘ᵥ unitorʳ {F = F}) ≈
  id₂ {F = F ∘ₚ idₚ {o = o} {p = p} {A = A}}
unitorʳ-isoˡ targetParameter = refl

unitorʳ-isoʳ :
  ∀ {o p : Level} {A B : Set o}
    {F : Para {o = o} {p = p} A B} →
  (unitorʳ {F = F} ∘ᵥ unitorʳ⁻¹ {F = F}) ≈ id₂ {F = F}
unitorʳ-isoʳ targetParameter = refl

associator-isoˡ :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  (associator⁻¹ {F = F} {G = G} {H = H} ∘ᵥ
   associator {F = F} {G = G} {H = H}) ≈
  id₂ {F = (H ∘ₚ G) ∘ₚ F}
associator-isoˡ targetParameter = refl

associator-isoʳ :
  ∀ {o p : Level} {A B C D : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D} →
  (associator {F = F} {G = G} {H = H} ∘ᵥ
   associator⁻¹ {F = F} {G = G} {H = H}) ≈
  id₂ {F = H ∘ₚ (G ∘ₚ F)}
associator-isoʳ targetParameter = refl

-- Naturality of the unitors and associator with respect to local
-- reparameterizations. The equation orientation matches NIHelper.commute.
unitorˡ-natural :
  ∀ {o p : Level} {A B : Set o}
    {F F′ : Para {o = o} {p = p} A B} →
  (α : Reparameterization F F′) →
  (unitorˡ {F = F′} ∘ᵥ
   (id₂ {F = idₚ {o = o} {p = p} {A = B}} ∘ₕ α)) ≈
  (α ∘ᵥ unitorˡ {F = F})
unitorˡ-natural α targetParameter = refl

unitorʳ-natural :
  ∀ {o p : Level} {A B : Set o}
    {F F′ : Para {o = o} {p = p} A B} →
  (α : Reparameterization F F′) →
  (unitorʳ {F = F′} ∘ᵥ
   (α ∘ₕ id₂ {F = idₚ {o = o} {p = p} {A = A}})) ≈
  (α ∘ᵥ unitorʳ {F = F})
unitorʳ-natural α targetParameter = refl

associator-natural :
  ∀ {o p : Level} {A B C D : Set o}
    {F F′ : Para {o = o} {p = p} A B}
    {G G′ : Para {o = o} {p = p} B C}
    {H H′ : Para {o = o} {p = p} C D} →
  (α : Reparameterization F F′) →
  (β : Reparameterization G G′) →
  (γ : Reparameterization H H′) →
  (associator {F = F′} {G = G′} {H = H′} ∘ᵥ
   ((γ ∘ₕ β) ∘ₕ α)) ≈
  ((γ ∘ₕ (β ∘ₕ α)) ∘ᵥ
   associator {F = F} {G = G} {H = H})
associator-natural α β γ targetParameter = refl

-- Mac Lane's triangle: reassociate past an identity or remove that identity
-- directly; both parameter maps insert the same unit value.
triangle :
  ∀ {o p : Level} {A B C : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C} →
  ((id₂ {F = G} ∘ₕ unitorˡ {F = F}) ∘ᵥ
   associator
     {F = F}
     {G = idₚ {o = o} {p = p} {A = B}}
     {H = G}) ≈
  (unitorʳ {F = G} ∘ₕ id₂ {F = F})
triangle targetParameter = refl

-- Mac Lane's pentagon: all ways of reassociating four sequential parameter
-- products induce the same map from the fully right-associated target to the
-- fully left-associated source.
pentagon :
  ∀ {o p : Level} {A B C D E : Set o}
    {F : Para {o = o} {p = p} A B}
    {G : Para {o = o} {p = p} B C}
    {H : Para {o = o} {p = p} C D}
    {I : Para {o = o} {p = p} D E} →
  ((id₂ {F = I} ∘ₕ associator {F = F} {G = G} {H = H}) ∘ᵥ
   (associator {F = F} {G = H ∘ₚ G} {H = I} ∘ᵥ
    (associator {F = G} {G = H} {H = I} ∘ₕ id₂ {F = F}))) ≈
  (associator {F = G ∘ₚ F} {G = H} {H = I} ∘ᵥ
   associator {F = F} {G = G} {H = I ∘ₚ H})
pentagon targetParameter = refl
