{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Laws where

open import Level using (Level)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Morphism.Reasoning as MorphismReasoning

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

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
      A B D E : 𝒞.Obj
      F F′ : Para 𝒜 A B
      G G′ : Para 𝒜 B D
      H H′ : Para 𝒜 D E

  -- Cancellation transports evaluator preservation across an invertible
  -- parameter map. This derives each forward G.1 structural cell from its
  -- more direct inverse cell.
  forward-from-inverse :
    ∀ {P Q : M.Obj} {X Y : 𝒞.Obj}
      {from : Q M.⇒ P} {to : P M.⇒ Q} →
    (isoʳ : from M.∘ to M.≈ M.id) →
    {f : (P 𝒜.⊙₀ X) 𝒞.⇒ Y}
    {g : (Q 𝒜.⊙₀ X) 𝒞.⇒ Y} →
    g 𝒞.≈ f 𝒞.∘ (from 𝒜.⊙₁ 𝒞.id) →
    f 𝒞.≈ g 𝒞.∘ (to 𝒜.⊙₁ 𝒞.id)
  forward-from-inverse
    {P = P} {Q = Q} {X = X}
    {from = from} {to = to} isoʳ g≈f∘from =
    𝒞.Equiv.sym 𝒞.identityʳ
      ○ (refl⟩∘⟨ 𝒞.Equiv.sym action-cancel)
      ○ 𝒞.sym-assoc
      ○ (𝒞.Equiv.sym g≈f∘from ⟩∘⟨refl)
    where
      open 𝒞.HomReasoning

      action-cancel :
        (𝒜.action.F₁ (from , 𝒞.id {A = X}) 𝒞.∘
          𝒜.action.F₁ (to , 𝒞.id)) 𝒞.≈ 𝒞.id
      action-cancel =
        𝒞.Equiv.sym 𝒜.action.homomorphism
          ○ 𝒜.action.F-resp-≈ (isoʳ , 𝒞.identity²)
          ○ 𝒜.action.identity

  unitorˡ⁻¹-preserves :
    run (idₚ ∘ₚ F) 𝒞.≈
      run F 𝒞.∘ (V.unitorˡ.from 𝒜.⊙₁ 𝒞.id)
  unitorˡ⁻¹-preserves {F = F} = begin
    run (idₚ ∘ₚ F)
      ≈⟨ 𝒞.sym-assoc ⟩
    (𝒜.unitor.⇒.η _ 𝒞.∘ (M.id 𝒜.⊙₁ run F)) 𝒞.∘
      𝒜.associator.⇒.η
        ((V.unit , Parameters F) , _)
      ≈⟨ 𝒜.unitor.⇒.commute (run F) ⟩∘⟨refl ⟩
    (run F 𝒞.∘ 𝒜.unitor.⇒.η _) 𝒞.∘
      𝒜.associator.⇒.η
        ((V.unit , Parameters F) , _)
      ≈⟨ 𝒞.assoc ⟩
    run F 𝒞.∘
      (𝒜.unitor.⇒.η _ 𝒞.∘
        𝒜.associator.⇒.η
          ((V.unit , Parameters F) , _))
      ≈⟨ refl⟩∘⟨ 𝒜.unitorˡ-coherence ⟩
    run F 𝒞.∘ (V.unitorˡ.from 𝒜.⊙₁ 𝒞.id)
      ∎
    where
      open 𝒞.HomReasoning

  unitorˡ⁻¹ : Reparameterization 𝒜 F (idₚ ∘ₚ F)
  unitorˡ⁻¹ = mkReparameterization
    V.unitorˡ.from
    unitorˡ⁻¹-preserves

  unitorˡ-preserves :
    run F 𝒞.≈ run (idₚ ∘ₚ F) 𝒞.∘
      (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
  unitorˡ-preserves = forward-from-inverse
    V.unitorˡ.isoʳ unitorˡ⁻¹-preserves

  unitorˡ : Reparameterization 𝒜 (idₚ ∘ₚ F) F
  unitorˡ = mkReparameterization
    V.unitorˡ.to
    unitorˡ-preserves

  unitorʳ⁻¹-preserves :
    run (F ∘ₚ idₚ) 𝒞.≈
      run F 𝒞.∘ (V.unitorʳ.from 𝒜.⊙₁ 𝒞.id)
  unitorʳ⁻¹-preserves {F = F} =
    𝒞.∘-resp-≈ʳ 𝒜.triangle

  unitorʳ⁻¹ : Reparameterization 𝒜 F (F ∘ₚ idₚ)
  unitorʳ⁻¹ = mkReparameterization
    V.unitorʳ.from
    unitorʳ⁻¹-preserves

  unitorʳ-preserves :
    run F 𝒞.≈ run (F ∘ₚ idₚ) 𝒞.∘
      (V.unitorʳ.to 𝒜.⊙₁ 𝒞.id)
  unitorʳ-preserves = forward-from-inverse
    V.unitorʳ.isoʳ unitorʳ⁻¹-preserves

  unitorʳ : Reparameterization 𝒜 (F ∘ₚ idₚ) F
  unitorʳ = mkReparameterization
    V.unitorʳ.to
    unitorʳ-preserves

  -- Naturality of the action associator with identities in its parameter
  -- positions, normalized using tensor's identity law.
  associator-id-natural :
    ∀ {P Q : M.Obj} {X Y : 𝒞.Obj} (f : X 𝒞.⇒ Y) →
    𝒜.associator.⇒.η ((P , Q) , Y) 𝒞.∘
      (M.id 𝒜.⊙₁ f)
      𝒞.≈
    (M.id 𝒜.⊙₁ (M.id 𝒜.⊙₁ f)) 𝒞.∘
      𝒜.associator.⇒.η ((P , Q) , X)
  associator-id-natural f =
    (refl⟩∘⟨ 𝒞.Equiv.sym
      (𝒜.action.F-resp-≈
        (V.⊗.identity , 𝒞.Equiv.refl)))
      ○ 𝒜.associator.⇒.commute (((M.id , M.id) , f))
    where
      open 𝒞.HomReasoning

  merge-fixed-action :
    ∀ {P : M.Obj} {X Y Z : 𝒞.Obj}
      (f : Y 𝒞.⇒ Z) (h : X 𝒞.⇒ Y) →
    ((M.id {A = P} 𝒜.⊙₁ f) 𝒞.∘
      (M.id {A = P} 𝒜.⊙₁ h))
      𝒞.≈
    (M.id {A = P} 𝒜.⊙₁ (f 𝒞.∘ h))
  merge-fixed-action {P = P} f h =
    𝒞.Equiv.sym 𝒜.action.homomorphism
      ○ 𝒜.action.F-resp-≈
        (M.identity² , 𝒞.Equiv.refl)
    where
      open 𝒞.HomReasoning

  -- Inverse associator preservation is the action pentagon combined with
  -- associator naturality and action functoriality.
  associator⁻¹-preserves :
    ∀ {A B D E : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D}
      {H : Para 𝒜 D E} →
    run ((H ∘ₚ G) ∘ₚ F) 𝒞.≈
      run (H ∘ₚ (G ∘ₚ F)) 𝒞.∘
        (V.associator.from 𝒜.⊙₁ 𝒞.id)
  associator⁻¹-preserves {A = A} {B = B} {F = F} {G = G} {H = H} = begin
    run ((H ∘ₚ G) ∘ₚ F)
      ≈⟨ 𝒞.assoc ⟩
    run H 𝒞.∘
      (((M.id 𝒜.⊙₁ run G) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters H , Parameters G) , B)) 𝒞.∘
      ((M.id 𝒜.⊙₁ run F) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters H V.⊗₀ Parameters G , Parameters F) , A)))
      ≈⟨ 𝒞.∘-resp-≈ʳ 𝒞.assoc ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run G) 𝒞.∘
        (𝒜.associator.⇒.η
          ((Parameters H , Parameters G) , B) 𝒞.∘
        ((M.id 𝒜.⊙₁ run F) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters H V.⊗₀ Parameters G , Parameters F) , A))))
      ≈⟨ 𝒞.∘-resp-≈ʳ (refl⟩∘⟨
          MorphismReasoning.pullˡ 𝒞
            (associator-id-natural (run F))) ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run G) 𝒞.∘
        (((M.id 𝒜.⊙₁ (M.id 𝒜.⊙₁ run F)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters H , Parameters G) , Parameters F 𝒜.⊙₀ A)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters H V.⊗₀ Parameters G , Parameters F) , A)))
      ≈⟨ 𝒞.∘-resp-≈ʳ (refl⟩∘⟨ 𝒞.assoc) ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run G) 𝒞.∘
        ((M.id 𝒜.⊙₁ (M.id 𝒜.⊙₁ run F)) 𝒞.∘
          (𝒜.associator.⇒.η
            ((Parameters H , Parameters G) , Parameters F 𝒜.⊙₀ A) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters H V.⊗₀ Parameters G , Parameters F) , A))))
      ≈˘⟨ 𝒞.∘-resp-≈ʳ (refl⟩∘⟨
          (refl⟩∘⟨ 𝒜.pentagon)) ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run G) 𝒞.∘
        ((M.id 𝒜.⊙₁ (M.id 𝒜.⊙₁ run F)) 𝒞.∘
          ((M.id 𝒜.⊙₁
            𝒜.associator.⇒.η
              ((Parameters G , Parameters F) , A)) 𝒞.∘
          (𝒜.associator.⇒.η
            ((Parameters H , Parameters G V.⊗₀ Parameters F) , A) 𝒞.∘
          (V.associator.from 𝒜.⊙₁ 𝒞.id)))))
      ≈⟨ 𝒞.∘-resp-≈ʳ (refl⟩∘⟨
          MorphismReasoning.pullˡ 𝒞
            (merge-fixed-action
              (M.id {A = Parameters G} 𝒜.⊙₁ run F)
              (𝒜.associator.⇒.η
                ((Parameters G , Parameters F) , A)))) ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run G) 𝒞.∘
        ((M.id 𝒜.⊙₁
          ((M.id 𝒜.⊙₁ run F) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters G , Parameters F) , A))) 𝒞.∘
        (𝒜.associator.⇒.η
          ((Parameters H , Parameters G V.⊗₀ Parameters F) , A) 𝒞.∘
        (V.associator.from 𝒜.⊙₁ 𝒞.id))))
      ≈⟨ 𝒞.∘-resp-≈ʳ
          (MorphismReasoning.pullˡ 𝒞
            (merge-fixed-action
              (run G)
              ((M.id {A = Parameters G} 𝒜.⊙₁ run F) 𝒞.∘
                𝒜.associator.⇒.η
                  ((Parameters G , Parameters F) , A)))) ⟩
    run H 𝒞.∘
      ((M.id 𝒜.⊙₁ run (G ∘ₚ F)) 𝒞.∘
        (𝒜.associator.⇒.η
          ((Parameters H , Parameters G V.⊗₀ Parameters F) , A) 𝒞.∘
        (V.associator.from 𝒜.⊙₁ 𝒞.id)))
      ≈⟨ 𝒞.∘-resp-≈ʳ 𝒞.sym-assoc ⟩
    run H 𝒞.∘
      (((M.id 𝒜.⊙₁ run (G ∘ₚ F)) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters H , Parameters G V.⊗₀ Parameters F) , A)) 𝒞.∘
      (V.associator.from 𝒜.⊙₁ 𝒞.id))
      ≈⟨ 𝒞.sym-assoc ⟩
    run (H ∘ₚ (G ∘ₚ F)) 𝒞.∘
      (V.associator.from 𝒜.⊙₁ 𝒞.id)
      ∎
    where
      open 𝒞.HomReasoning

  associator⁻¹ :
    ∀ {A B D E : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D}
      {H : Para 𝒜 D E} →
    Reparameterization 𝒜
      (H ∘ₚ (G ∘ₚ F))
      ((H ∘ₚ G) ∘ₚ F)
  associator⁻¹ = mkReparameterization
    V.associator.from
    associator⁻¹-preserves

  associator-preserves :
    run (H ∘ₚ (G ∘ₚ F)) 𝒞.≈
      run ((H ∘ₚ G) ∘ₚ F) 𝒞.∘
        (V.associator.to 𝒜.⊙₁ 𝒞.id)
  associator-preserves = forward-from-inverse
    V.associator.isoʳ associator⁻¹-preserves

  associator :
    ∀ {A B D E : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D}
      {H : Para 𝒜 D E} →
    Reparameterization 𝒜
      ((H ∘ₚ G) ∘ₚ F)
      (H ∘ₚ (G ∘ₚ F))
  associator = mkReparameterization
    V.associator.to
    associator-preserves

  unitorˡ-isoˡ :
    (unitorˡ⁻¹ {F = F} ∘ᵥ unitorˡ {F = F}) ≈
      id₂ {F = idₚ ∘ₚ F}
  unitorˡ-isoˡ = V.unitorˡ.isoˡ

  unitorˡ-isoʳ :
    (unitorˡ {F = F} ∘ᵥ unitorˡ⁻¹ {F = F}) ≈ id₂ {F = F}
  unitorˡ-isoʳ = V.unitorˡ.isoʳ

  unitorʳ-isoˡ :
    (unitorʳ⁻¹ {F = F} ∘ᵥ unitorʳ {F = F}) ≈
      id₂ {F = F ∘ₚ idₚ}
  unitorʳ-isoˡ = V.unitorʳ.isoˡ

  unitorʳ-isoʳ :
    (unitorʳ {F = F} ∘ᵥ unitorʳ⁻¹ {F = F}) ≈ id₂ {F = F}
  unitorʳ-isoʳ = V.unitorʳ.isoʳ

  associator-isoˡ :
    (associator⁻¹ {F = F} {G = G} {H = H} ∘ᵥ
      associator {F = F} {G = G} {H = H}) ≈
    id₂ {F = (H ∘ₚ G) ∘ₚ F}
  associator-isoˡ = V.associator.isoˡ

  associator-isoʳ :
    (associator {F = F} {G = G} {H = H} ∘ᵥ
      associator⁻¹ {F = F} {G = G} {H = H}) ≈
    id₂ {F = H ∘ₚ (G ∘ₚ F)}
  associator-isoʳ = V.associator.isoʳ

  unitorˡ-natural :
    (α : Reparameterization 𝒜 F F′) →
    (unitorˡ {F = F′} ∘ᵥ
      (id₂ {F = idₚ} ∘ₕ α)) ≈
    (α ∘ᵥ unitorˡ {F = F})
  unitorˡ-natural α = M.Equiv.sym V.unitorˡ-commute-to

  unitorʳ-natural :
    (α : Reparameterization 𝒜 F F′) →
    (unitorʳ {F = F′} ∘ᵥ
      (α ∘ₕ id₂ {F = idₚ})) ≈
    (α ∘ᵥ unitorʳ {F = F})
  unitorʳ-natural α = M.Equiv.sym V.unitorʳ-commute-to

  associator-natural :
    ∀ {A B D E : 𝒞.Obj}
      {F F′ : Para 𝒜 A B}
      {G G′ : Para 𝒜 B D}
      {H H′ : Para 𝒜 D E} →
    (α : Reparameterization 𝒜 F F′) →
    (β : Reparameterization 𝒜 G G′) →
    (γ : Reparameterization 𝒜 H H′) →
    (associator {F = F′} {G = G′} {H = H′} ∘ᵥ
      ((γ ∘ₕ β) ∘ₕ α)) ≈
    ((γ ∘ₕ (β ∘ₕ α)) ∘ᵥ
      associator {F = F} {G = G} {H = H})
  associator-natural α β γ = M.Equiv.sym V.assoc-commute-to

  triangle :
    ∀ {A B D : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D} →
    ((id₂ {F = G} ∘ₕ unitorˡ {F = F}) ∘ᵥ
      associator {F = F} {G = idₚ} {H = G}) ≈
    (unitorʳ {F = G} ∘ₕ id₂ {F = F})
  triangle = MonoidalUtilities.triangle-inv V

  pentagon :
    ∀ {A B D E : 𝒞.Obj} {X : 𝒞.Obj}
      {F : Para 𝒜 A B}
      {G : Para 𝒜 B D}
      {H : Para 𝒜 D E}
      {I : Para 𝒜 E X} →
    ((id₂ {F = I} ∘ₕ associator {F = F} {G = G} {H = H}) ∘ᵥ
      (associator {F = F} {G = H ∘ₚ G} {H = I} ∘ᵥ
      (associator {F = G} {G = H} {H = I} ∘ₕ id₂ {F = F}))) ≈
    (associator {F = G ∘ₚ F} {G = H} {H = I} ∘ᵥ
      associator {F = F} {G = G} {H = I ∘ₚ H})
  pentagon = MonoidalUtilities.pentagon-inv V
