{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal.Laws where

open import Level using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Properties as MonoidalProperties
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Morphism.Reasoning as MorphismReasoning

open import ParaForge.Para.Monoidal
open import ParaForge.Para.Monoidal.Reparameterization

private
  variable
    o ℓ e : Level

-- Structural cells are induced by the ambient monoidal isomorphisms. Their
-- parameter maps point backwards relative to the displayed 2-cell, as required
-- by the G.1 orientation.
module _ {C : Category o ℓ e} {M : Monoidal C} where

  private
    module C = Category C
    module MC = Monoidal M

  open C using (Obj; id; _∘_)
  open MC using (_⊗₀_; _⊗₁_; unit)

  private
    variable
      A B D E : Obj
      F F′ : Para M A B
      G G′ : Para M B D
      H H′ : Para M D E

  -- If an evaluator equation is known in the forward direction of a parameter
  -- isomorphism, cancellation derives the equation needed by the reverse G.1
  -- cell. This keeps each structural preservation argument single-sourced.
  forward-from-inverse :
    ∀ {P Q X Y : Obj}
      {from : Q C.⇒ P} {to : P C.⇒ Q}
      (isoʳ : from ∘ to C.≈ id)
      {f : P ⊗₀ X C.⇒ Y}
      {g : Q ⊗₀ X C.⇒ Y} →
    g C.≈ f ∘ (from ⊗₁ id) →
    f C.≈ g ∘ (to ⊗₁ id)
  forward-from-inverse isoʳ g≈f∘from =
    C.Equiv.sym C.identityʳ
      ○ C.∘-resp-≈ʳ (C.Equiv.sym
          (MonoidalReasoning.⊗-cancel M isoʳ C.identity²))
      ○ C.sym-assoc
      ○ C.∘-resp-≈ˡ (C.Equiv.sym g≈f∘from)
    where
      open C.HomReasoning

  -- Left unitor inverse: F ⇒ (idₚ ∘ₚ F). Its parameter map is
  -- unitorˡ.from : I ⊗ P ⇒ P.
  unitorˡ⁻¹-preserves :
    run (idₚ ∘ₚ F) C.≈
      run F ∘ (MC.unitorˡ.from ⊗₁ id)
  unitorˡ⁻¹-preserves {F = F} = begin
    run (idₚ ∘ₚ F)
      ≈⟨ C.sym-assoc ⟩
    (MC.unitorˡ.from ∘ (id ⊗₁ run F)) ∘ MC.associator.from
      ≈⟨ MC.unitorˡ-commute-from ⟩∘⟨refl ⟩
    (run F ∘ MC.unitorˡ.from) ∘ MC.associator.from
      ≈⟨ C.assoc ⟩
    run F ∘ (MC.unitorˡ.from ∘ MC.associator.from)
      ≈⟨ C.Equiv.refl ⟩∘⟨ MonoidalProperties.coherence₁ M ⟩
    run F ∘ (MC.unitorˡ.from ⊗₁ id)
      ∎
    where
      open C.HomReasoning

  unitorˡ⁻¹ : Reparameterization M F (idₚ ∘ₚ F)
  unitorˡ⁻¹ = mkReparameterization
    MC.unitorˡ.from
    unitorˡ⁻¹-preserves

  -- Left unitor: (idₚ ∘ₚ F) ⇒ F. G.1 reverses the parameter map, so this
  -- uses unitorˡ.to : P ⇒ I ⊗ P.
  unitorˡ-preserves :
    run F C.≈ run (idₚ ∘ₚ F) ∘ (MC.unitorˡ.to ⊗₁ id)
  unitorˡ-preserves = forward-from-inverse
    MC.unitorˡ.isoʳ unitorˡ⁻¹-preserves

  unitorˡ : Reparameterization M (idₚ ∘ₚ F) F
  unitorˡ = mkReparameterization
    MC.unitorˡ.to
    unitorˡ-preserves

  -- Right unitor inverse: F ⇒ (F ∘ₚ idₚ). The monoidal triangle is exactly
  -- the evaluator equation after expanding generic Para composition.
  unitorʳ⁻¹-preserves :
    run (F ∘ₚ idₚ) C.≈
      run F ∘ (MC.unitorʳ.from ⊗₁ id)
  unitorʳ⁻¹-preserves {F = F} =
    C.∘-resp-≈ʳ MC.triangle

  unitorʳ⁻¹ : Reparameterization M F (F ∘ₚ idₚ)
  unitorʳ⁻¹ = mkReparameterization
    MC.unitorʳ.from
    unitorʳ⁻¹-preserves

  unitorʳ-preserves :
    run F C.≈ run (F ∘ₚ idₚ) ∘ (MC.unitorʳ.to ⊗₁ id)
  unitorʳ-preserves = forward-from-inverse
    MC.unitorʳ.isoʳ unitorʳ⁻¹-preserves

  unitorʳ : Reparameterization M (F ∘ₚ idₚ) F
  unitorʳ = mkReparameterization
    MC.unitorʳ.to
    unitorʳ-preserves

  -- Naturality of the monoidal associator with identities in its first two
  -- positions, normalized to the identity on their tensor product.
  associator-id-natural :
    ∀ {P Q X Y : Obj} (f : X C.⇒ Y) →
    MC.associator.from {X = P} {Y = Q} {Z = Y} ∘ (id ⊗₁ f) C.≈
      (id ⊗₁ (id ⊗₁ f)) ∘
        MC.associator.from {X = P} {Y = Q} {Z = X}
  associator-id-natural f = begin
    MC.associator.from ∘ (id ⊗₁ f)
      ≈˘⟨ C.Equiv.refl ⟩∘⟨
          MonoidalReasoning.⊗-resp-≈ M
            (Monoidal.⊗.identity M) C.Equiv.refl ⟩
    MC.associator.from ∘ ((id ⊗₁ id) ⊗₁ f)
      ≈⟨ MC.assoc-commute-from ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ MC.associator.from
      ∎
    where
      open C.HomReasoning

  -- Associator inverse: H ∘ₚ (G ∘ₚ F) ⇒ (H ∘ₚ G) ∘ₚ F. Expanding both
  -- evaluators reduces the equation to associator naturality, tensor
  -- functoriality, and the monoidal pentagon.
  associator⁻¹-preserves :
    ∀ {A B D E : Obj}
      {F : Para M A B}
      {G : Para M B D}
      {H : Para M D E} →
    run ((H ∘ₚ G) ∘ₚ F) C.≈
      run (H ∘ₚ (G ∘ₚ F)) ∘ (MC.associator.from ⊗₁ id)
  associator⁻¹-preserves {F = F} {G = G} {H = H} = begin
    run ((H ∘ₚ G) ∘ₚ F)
      ≈⟨ C.assoc ⟩
    run H ∘ (((id ⊗₁ run G) ∘ MC.associator.from) ∘
      ((id ⊗₁ run F) ∘ MC.associator.from))
      ≈⟨ C.∘-resp-≈ʳ C.assoc ⟩
    run H ∘ ((id ⊗₁ run G) ∘
      (MC.associator.from ∘
      ((id ⊗₁ run F) ∘ MC.associator.from)))
      ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
          (MorphismReasoning.pullˡ C
            (associator-id-natural
              {P = Parameters H} {Q = Parameters G} (run F)))) ⟩
    run H ∘ ((id ⊗₁ run G) ∘
      (((id ⊗₁ (id ⊗₁ run F)) ∘ MC.associator.from) ∘
      MC.associator.from))
      ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.assoc) ⟩
    run H ∘ ((id ⊗₁ run G) ∘
      ((id ⊗₁ (id ⊗₁ run F)) ∘
      (MC.associator.from ∘ MC.associator.from)))
      ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
          (C.∘-resp-≈ʳ MC.pentagon)) ⟩
    run H ∘ ((id ⊗₁ run G) ∘
      ((id ⊗₁ (id ⊗₁ run F)) ∘
      ((id ⊗₁ MC.associator.from) ∘
      (MC.associator.from ∘ (MC.associator.from ⊗₁ id)))))
      ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
          (MorphismReasoning.pullˡ C
            (MonoidalReasoning.merge₂ˡ M))) ⟩
    run H ∘ ((id ⊗₁ run G) ∘
      ((id ⊗₁ ((id ⊗₁ run F) ∘ MC.associator.from)) ∘
      (MC.associator.from ∘ (MC.associator.from ⊗₁ id))))
      ≈⟨ C.∘-resp-≈ʳ
          (MorphismReasoning.pullˡ C
            (MonoidalReasoning.merge₂ˡ M)) ⟩
    run H ∘ ((id ⊗₁ run (G ∘ₚ F)) ∘
      (MC.associator.from ∘ (MC.associator.from ⊗₁ id)))
      ≈⟨ C.∘-resp-≈ʳ C.sym-assoc ⟩
    run H ∘ (((id ⊗₁ run (G ∘ₚ F)) ∘ MC.associator.from) ∘
      (MC.associator.from ⊗₁ id))
      ≈⟨ C.sym-assoc ⟩
    run (H ∘ₚ (G ∘ₚ F)) ∘ (MC.associator.from ⊗₁ id)
      ∎
    where
      open C.HomReasoning

  associator⁻¹ :
    ∀ {A B D E : Obj}
      {F : Para M A B}
      {G : Para M B D}
      {H : Para M D E} →
    Reparameterization M
      (H ∘ₚ (G ∘ₚ F))
      ((H ∘ₚ G) ∘ₚ F)
  associator⁻¹ = mkReparameterization
    MC.associator.from
    associator⁻¹-preserves

  -- Forward associator: ((H ∘ₚ G) ∘ₚ F) ⇒ H ∘ₚ (G ∘ₚ F).
  -- Its backwards parameter map is associator.to.
  associator-preserves :
    run (H ∘ₚ (G ∘ₚ F)) C.≈
      run ((H ∘ₚ G) ∘ₚ F) ∘ (MC.associator.to ⊗₁ id)
  associator-preserves = forward-from-inverse
    MC.associator.isoʳ associator⁻¹-preserves

  associator :
    ∀ {A B D E : Obj}
      {F : Para M A B}
      {G : Para M B D}
      {H : Para M D E} →
    Reparameterization M
      ((H ∘ₚ G) ∘ₚ F)
      (H ∘ₚ (G ∘ₚ F))
  associator = mkReparameterization
    MC.associator.to
    associator-preserves

  -- The structural cells are invertible because cell equality observes only
  -- their parameter maps, where the ambient monoidal isomorphism laws apply.
  unitorˡ-isoˡ :
    (unitorˡ⁻¹ {F = F} ∘ᵥ unitorˡ {F = F}) ≈
      id₂ {F = idₚ ∘ₚ F}
  unitorˡ-isoˡ = MC.unitorˡ.isoˡ

  unitorˡ-isoʳ :
    (unitorˡ {F = F} ∘ᵥ unitorˡ⁻¹ {F = F}) ≈ id₂ {F = F}
  unitorˡ-isoʳ = MC.unitorˡ.isoʳ

  unitorʳ-isoˡ :
    (unitorʳ⁻¹ {F = F} ∘ᵥ unitorʳ {F = F}) ≈
      id₂ {F = F ∘ₚ idₚ}
  unitorʳ-isoˡ = MC.unitorʳ.isoˡ

  unitorʳ-isoʳ :
    (unitorʳ {F = F} ∘ᵥ unitorʳ⁻¹ {F = F}) ≈ id₂ {F = F}
  unitorʳ-isoʳ = MC.unitorʳ.isoʳ

  associator-isoˡ :
    (associator⁻¹ {F = F} {G = G} {H = H} ∘ᵥ
      associator {F = F} {G = G} {H = H}) ≈
    id₂ {F = (H ∘ₚ G) ∘ₚ F}
  associator-isoˡ = MC.associator.isoˡ

  associator-isoʳ :
    (associator {F = F} {G = G} {H = H} ∘ᵥ
      associator⁻¹ {F = F} {G = G} {H = H}) ≈
    id₂ {F = H ∘ₚ (G ∘ₚ F)}
  associator-isoʳ = MC.associator.isoʳ

  -- Naturality is inherited from the reverse directions of the monoidal
  -- isomorphisms because G.1 cells reverse their parameter morphisms.
  unitorˡ-natural :
    (α : Reparameterization M F F′) →
    (unitorˡ {F = F′} ∘ᵥ
      (id₂ {F = idₚ} ∘ₕ α)) ≈
    (α ∘ᵥ unitorˡ {F = F})
  unitorˡ-natural α = C.Equiv.sym MC.unitorˡ-commute-to

  unitorʳ-natural :
    (α : Reparameterization M F F′) →
    (unitorʳ {F = F′} ∘ᵥ
      (α ∘ₕ id₂ {F = idₚ})) ≈
    (α ∘ᵥ unitorʳ {F = F})
  unitorʳ-natural α = C.Equiv.sym MC.unitorʳ-commute-to

  associator-natural :
    ∀ {A B D E : Obj}
      {F F′ : Para M A B}
      {G G′ : Para M B D}
      {H H′ : Para M D E} →
    (α : Reparameterization M F F′) →
    (β : Reparameterization M G G′) →
    (γ : Reparameterization M H H′) →
    (associator {F = F′} {G = G′} {H = H′} ∘ᵥ
      ((γ ∘ₕ β) ∘ₕ α)) ≈
    ((γ ∘ₕ (β ∘ₕ α)) ∘ᵥ
      associator {F = F} {G = G} {H = H})
  associator-natural α β γ = C.Equiv.sym MC.assoc-commute-to

  -- At the observable parameter-map level these are exactly the inverse
  -- triangle and pentagon supplied by the monoidal structure.
  triangle :
    ∀ {A B D : Obj}
      {F : Para M A B}
      {G : Para M B D} →
    ((id₂ {F = G} ∘ₕ unitorˡ {F = F}) ∘ᵥ
      associator {F = F} {G = idₚ} {H = G}) ≈
    (unitorʳ {F = G} ∘ₕ id₂ {F = F})
  triangle = MonoidalUtilities.triangle-inv M

  pentagon :
    ∀ {A B D E : Obj} {X : Obj}
      {F : Para M A B}
      {G : Para M B D}
      {H : Para M D E}
      {I : Para M E X} →
    ((id₂ {F = I} ∘ₕ associator {F = F} {G = G} {H = H}) ∘ᵥ
      (associator {F = F} {G = H ∘ₚ G} {H = I} ∘ᵥ
      (associator {F = G} {G = H} {H = I} ∘ₕ id₂ {F = F}))) ≈
    (associator {F = G ∘ₚ F} {G = H} {H = I} ∘ᵥ
      associator {F = F} {G = G} {H = I ∘ₚ H})
  pentagon = MonoidalUtilities.pentagon-inv M
