{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Reparameterization where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning

open import ParaForge.Actegory using (Actegory)
open import ParaForge.Para.Actegory

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- A G.1 cell retains its target-to-source parameter morphism in M. Evaluator
-- preservation is measured in C after acting on that map and the identity.
module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  (𝒜 : Actegory V 𝒞) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module 𝒜 = Actegory 𝒜

  private
    variable
      A B : 𝒞.Obj

  record Reparameterization (F G : Para 𝒜 A B) : Set (ℓₘ ⊔ e𝒞) where
    constructor mkReparameterization
    field
      mapParameters : Parameters G M.⇒ Parameters F
      preserves-run :
        run G 𝒞.≈ run F 𝒞.∘ (mapParameters 𝒜.⊙₁ 𝒞.id)

open Reparameterization public

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞} where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module 𝒜 = Actegory 𝒜

  private
    variable
      A B D : 𝒞.Obj
      F G H I : Para 𝒜 A B

  infix 4 _≈_

  -- Cell equality observes only the parameter morphism in M.
  _≈_ : Reparameterization 𝒜 F G → Reparameterization 𝒜 F G → Set eₘ
  α ≈ β = mapParameters α M.≈ mapParameters β

  ≈-refl : (α : Reparameterization 𝒜 F G) → α ≈ α
  ≈-refl α = M.Equiv.refl

  ≈-sym : {α β : Reparameterization 𝒜 F G} → α ≈ β → β ≈ α
  ≈-sym = M.Equiv.sym

  ≈-trans : {α β γ : Reparameterization 𝒜 F G} →
    α ≈ β → β ≈ γ → α ≈ γ
  ≈-trans = M.Equiv.trans

  reparameterizationSetoid :
    (F G : Para 𝒜 A B) → Setoid (ℓₘ ⊔ e𝒞) eₘ
  reparameterizationSetoid F G = record
    { Carrier = Reparameterization 𝒜 F G
    ; _≈_ = _≈_
    ; isEquivalence = record
        { refl = M.Equiv.refl
        ; sym = M.Equiv.sym
        ; trans = M.Equiv.trans
        }
    }

  identityPreserves :
    run F 𝒞.≈ run F 𝒞.∘ (M.id 𝒜.⊙₁ 𝒞.id)
  identityPreserves {F = F} = begin
    run F                              ≈˘⟨ 𝒞.identityʳ ⟩
    run F 𝒞.∘ 𝒞.id                   ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒜.action.identity ⟩
    run F 𝒞.∘ (M.id 𝒜.⊙₁ 𝒞.id)     ∎
    where
      open 𝒞.HomReasoning

  id₂ : Reparameterization 𝒜 F F
  id₂ = mkReparameterization M.id identityPreserves

  -- Functoriality of the action combines consecutive parameter changes.
  merge-action :
    ∀ {P Q R : M.Obj} {X : 𝒞.Obj}
      (r : Q M.⇒ P) (s : R M.⇒ Q) →
    ((r 𝒜.⊙₁ 𝒞.id {A = X}) 𝒞.∘ (s 𝒜.⊙₁ 𝒞.id))
      𝒞.≈
    ((r M.∘ s) 𝒜.⊙₁ 𝒞.id)
  merge-action r s = 𝒞.Equiv.sym
    (𝒜.action.F-resp-≈
      (M.Equiv.refl , 𝒞.Equiv.sym 𝒞.identity²)
      ○ 𝒜.action.homomorphism)
    where
      open 𝒞.HomReasoning

  verticalPreserves :
    (β : Reparameterization 𝒜 G H) →
    (α : Reparameterization 𝒜 F G) →
    run H 𝒞.≈
      run F 𝒞.∘
        ((mapParameters α M.∘ mapParameters β) 𝒜.⊙₁ 𝒞.id)
  verticalPreserves β α =
    preserves-run β
      ○ (preserves-run α ⟩∘⟨refl)
      ○ 𝒞.assoc
      ○ (refl⟩∘⟨
          merge-action (mapParameters α) (mapParameters β))
    where
      open 𝒞.HomReasoning

  infixr 7 _∘ᵥ_

  _∘ᵥ_ :
    Reparameterization 𝒜 G H →
    Reparameterization 𝒜 F G →
    Reparameterization 𝒜 F H
  β ∘ᵥ α = mkReparameterization
    (mapParameters α M.∘ mapParameters β)
    (verticalPreserves β α)

  ∘ᵥ-resp-≈ :
    {α α′ : Reparameterization 𝒜 F G} →
    {β β′ : Reparameterization 𝒜 G H} →
    β ≈ β′ → α ≈ α′ →
    (β ∘ᵥ α) ≈ (β′ ∘ᵥ α′)
  ∘ᵥ-resp-≈ β≈β′ α≈α′ = M.∘-resp-≈ α≈α′ β≈β′

  ∘ᵥ-identityˡ : (α : Reparameterization 𝒜 F G) →
    (id₂ {F = G} ∘ᵥ α) ≈ α
  ∘ᵥ-identityˡ α = M.identityʳ

  ∘ᵥ-identityʳ : (α : Reparameterization 𝒜 F G) →
    (α ∘ᵥ id₂ {F = F}) ≈ α
  ∘ᵥ-identityʳ α = M.identityˡ

  ∘ᵥ-assoc :
    (γ : Reparameterization 𝒜 H I) →
    (β : Reparameterization 𝒜 G H) →
    (α : Reparameterization 𝒜 F G) →
    ((γ ∘ᵥ β) ∘ᵥ α) ≈ (γ ∘ᵥ (β ∘ᵥ α))
  ∘ᵥ-assoc γ β α = M.sym-assoc

  -- Two useful action-functor normalizations for horizontal preservation.
  merge-action-maps :
    ∀ {P P′ : M.Obj} {X Y : 𝒞.Obj}
      (r : P′ M.⇒ P) (f : X 𝒞.⇒ Y) →
    ((r 𝒜.⊙₁ 𝒞.id) 𝒞.∘ (M.id 𝒜.⊙₁ f))
      𝒞.≈ (r 𝒜.⊙₁ f)
  merge-action-maps r f =
    𝒞.Equiv.sym 𝒜.action.homomorphism
      ○ 𝒜.action.F-resp-≈
        (M.identityʳ , 𝒞.identityˡ)
    where
      open 𝒞.HomReasoning

  split-action-map :
    ∀ {P P′ : M.Obj} {X Y Z : 𝒞.Obj}
      (r : P′ M.⇒ P) (f : Y 𝒞.⇒ Z) (h : X 𝒞.⇒ Y) →
    (r 𝒜.⊙₁ (f 𝒞.∘ h))
      𝒞.≈
    ((M.id 𝒜.⊙₁ f) 𝒞.∘ (r 𝒜.⊙₁ h))
  split-action-map r f h =
    𝒜.action.F-resp-≈
      (M.Equiv.sym M.identityˡ , 𝒞.Equiv.refl)
      ○ 𝒜.action.homomorphism
    where
      open 𝒞.HomReasoning

  horizontalPreserves :
    ∀ {A B D : 𝒞.Obj}
      {F F′ : Para 𝒜 A B}
      {G G′ : Para 𝒜 B D} →
    (β : Reparameterization 𝒜 G G′) →
    (α : Reparameterization 𝒜 F F′) →
    run (G′ ∘ₚ F′) 𝒞.≈
      run (G ∘ₚ F) 𝒞.∘
        ((mapParameters β V.⊗₁ mapParameters α) 𝒜.⊙₁ 𝒞.id)
  horizontalPreserves
    {F = F} {F′ = F′} {G = G} {G′ = G′} β α = begin
    run (G′ ∘ₚ F′)
      ≈⟨ 𝒞.∘-resp-≈ˡ (preserves-run β) ⟩
    (run G 𝒞.∘ (mapParameters β 𝒜.⊙₁ 𝒞.id)) 𝒞.∘
      ((M.id 𝒜.⊙₁ run F′) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G′ , Parameters F′) , _))
      ≈⟨ 𝒞.assoc ⟩
    run G 𝒞.∘
      ((mapParameters β 𝒜.⊙₁ 𝒞.id) 𝒞.∘
        ((M.id 𝒜.⊙₁ run F′) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters G′ , Parameters F′) , _)))
      ≈⟨ 𝒞.∘-resp-≈ʳ 𝒞.sym-assoc ⟩
    run G 𝒞.∘
      (((mapParameters β 𝒜.⊙₁ 𝒞.id) 𝒞.∘
        (M.id 𝒜.⊙₁ run F′)) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G′ , Parameters F′) , _))
      ≈⟨ 𝒞.∘-resp-≈ʳ
          (merge-action-maps (mapParameters β) (run F′)
            ⟩∘⟨refl) ⟩
    run G 𝒞.∘
      ((mapParameters β 𝒜.⊙₁ run F′) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G′ , Parameters F′) , _))
      ≈⟨ 𝒞.∘-resp-≈ʳ
          ((𝒜.action.F-resp-≈
            (M.Equiv.refl , preserves-run α))
            ⟩∘⟨refl) ⟩
    run G 𝒞.∘
      ((mapParameters β 𝒜.⊙₁
        (run F 𝒞.∘ (mapParameters α 𝒜.⊙₁ 𝒞.id))) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G′ , Parameters F′) , _))
      ≈⟨ 𝒞.∘-resp-≈ʳ
          (split-action-map (mapParameters β) (run F)
            (mapParameters α 𝒜.⊙₁ 𝒞.id)
            ⟩∘⟨refl) ⟩
    run G 𝒞.∘
      (((M.id 𝒜.⊙₁ run F) 𝒞.∘
        (mapParameters β 𝒜.⊙₁
          (mapParameters α 𝒜.⊙₁ 𝒞.id))) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G′ , Parameters F′) , _))
      ≈⟨ 𝒞.∘-resp-≈ʳ 𝒞.assoc ⟩
    run G 𝒞.∘
      ((M.id 𝒜.⊙₁ run F) 𝒞.∘
        ((mapParameters β 𝒜.⊙₁
          (mapParameters α 𝒜.⊙₁ 𝒞.id)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters G′ , Parameters F′) , _)))
      ≈˘⟨ 𝒞.∘-resp-≈ʳ
          (refl⟩∘⟨
            𝒜.associator.⇒.commute
              (((mapParameters β , mapParameters α) , 𝒞.id))) ⟩
    run G 𝒞.∘
      ((M.id 𝒜.⊙₁ run F) 𝒞.∘
        (𝒜.associator.⇒.η
          ((Parameters G , Parameters F) , _) 𝒞.∘
        ((mapParameters β V.⊗₁ mapParameters α) 𝒜.⊙₁ 𝒞.id)))
      ≈⟨ 𝒞.∘-resp-≈ʳ 𝒞.sym-assoc ⟩
    run G 𝒞.∘
      (((M.id 𝒜.⊙₁ run F) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters G , Parameters F) , _)) 𝒞.∘
        ((mapParameters β V.⊗₁ mapParameters α) 𝒜.⊙₁ 𝒞.id))
      ≈⟨ 𝒞.sym-assoc ⟩
    run (G ∘ₚ F) 𝒞.∘
      ((mapParameters β V.⊗₁ mapParameters α) 𝒜.⊙₁ 𝒞.id)
      ∎
    where
      open 𝒞.HomReasoning

  infixr 11 _∘ₕ_

  _∘ₕ_ :
    ∀ {A B D : 𝒞.Obj}
      {F F′ : Para 𝒜 A B}
      {G G′ : Para 𝒜 B D} →
    Reparameterization 𝒜 G G′ →
    Reparameterization 𝒜 F F′ →
    Reparameterization 𝒜 (G ∘ₚ F) (G′ ∘ₚ F′)
  β ∘ₕ α = mkReparameterization
    (mapParameters β V.⊗₁ mapParameters α)
    (horizontalPreserves β α)

  ∘ₕ-resp-≈ :
    ∀ {A B D : 𝒞.Obj}
      {F F′ : Para 𝒜 A B}
      {G G′ : Para 𝒜 B D}
      {α α′ : Reparameterization 𝒜 F F′}
      {β β′ : Reparameterization 𝒜 G G′} →
    β ≈ β′ → α ≈ α′ →
    (β ∘ₕ α) ≈ (β′ ∘ₕ α′)
  ∘ₕ-resp-≈ = MonoidalReasoning.⊗-resp-≈ V

  ∘ₕ-identity :
    ∀ {A B D : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D} →
    (id₂ {F = G} ∘ₕ id₂ {F = F}) ≈ id₂ {F = G ∘ₚ F}
  ∘ₕ-identity = V.⊗.identity

  interchange :
    ∀ {A B D : 𝒞.Obj}
      {F₀ F₁ F₂ : Para 𝒜 A B}
      {G₀ G₁ G₂ : Para 𝒜 B D} →
    (β₁ : Reparameterization 𝒜 G₀ G₁) →
    (β₂ : Reparameterization 𝒜 G₁ G₂) →
    (α₁ : Reparameterization 𝒜 F₀ F₁) →
    (α₂ : Reparameterization 𝒜 F₁ F₂) →
    ((β₂ ∘ᵥ β₁) ∘ₕ (α₂ ∘ᵥ α₁)) ≈
      ((β₂ ∘ₕ α₂) ∘ᵥ (β₁ ∘ₕ α₁))
  interchange β₁ β₂ α₁ α₂ =
    MonoidalReasoning.⊗-distrib-over-∘ V
