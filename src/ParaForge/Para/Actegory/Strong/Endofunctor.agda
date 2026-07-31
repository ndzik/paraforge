{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Strong.Endofunctor where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)
open import Categories.Pseudofunctor using (Pseudofunctor)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Endofunctor
  using (StrongEndofunctor)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Hom using (Hom)
open import ParaForge.Para.Actegory.Laws using (merge-fixed-action)
open import ParaForge.Para.Actegory.Bicategory using (ParaActegory)
open import ParaForge.Para.Actegory.Restriction
  using (restrictParameters; restrictCell)
open import ParaForge.Para.Actegory.Sharing
  using
    ( ParameterComonoid; copyParameter
    ; untiedParameterPair; tieParameterPair
    )

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞}
  (S : StrongEndofunctor 𝒜) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module 𝒜 = Actegory 𝒜
    module S = StrongEndofunctor S

  private
    variable
      A B D : 𝒞.Obj
      K L N : Para 𝒜 A B

  -- Strength moves the unchanged parameter object through F.
  liftPara : Para 𝒜 A B → Para 𝒜 (S.F.F₀ A) (S.F.F₀ B)
  liftPara {A = A} K = mkPara
    (Parameters K)
    (S.F.F₁ (run K) 𝒞.∘ S.σ (Parameters K) A)

  lift-preserves :
    (α : Reparameterization 𝒜 K L) →
    run (liftPara L) 𝒞.≈
      run (liftPara K) 𝒞.∘
        (mapParameters α 𝒜.⊙₁ 𝒞.id)
  lift-preserves {K = K} {L = L} α = begin
    S.F.F₁ (run L) 𝒞.∘ S.σ (Parameters L) _
      ≈⟨ S.F.F-resp-≈ (preserves-run α) ⟩∘⟨refl ⟩
    S.F.F₁
      (run K 𝒞.∘
        (mapParameters α 𝒜.⊙₁ 𝒞.id)) 𝒞.∘
      S.σ (Parameters L) _
      ≈⟨ S.F.homomorphism ⟩∘⟨refl ⟩
    (S.F.F₁ (run K) 𝒞.∘
      S.F.F₁ (mapParameters α 𝒜.⊙₁ 𝒞.id)) 𝒞.∘
      S.σ (Parameters L) _
      ≈⟨ 𝒞.assoc ⟩
    S.F.F₁ (run K) 𝒞.∘
      (S.F.F₁ (mapParameters α 𝒜.⊙₁ 𝒞.id) 𝒞.∘
        S.σ (Parameters L) _)
      ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨
        S.strength-natural-id (mapParameters α) ⟩
    S.F.F₁ (run K) 𝒞.∘
      (S.σ (Parameters K) _ 𝒞.∘
        (mapParameters α 𝒜.⊙₁ 𝒞.id))
      ≈⟨ 𝒞.sym-assoc ⟩
    run (liftPara K) 𝒞.∘
      (mapParameters α 𝒜.⊙₁ 𝒞.id)
      ∎
    where
      open 𝒞.HomReasoning

  liftCell :
    Reparameterization 𝒜 K L →
    Reparameterization 𝒜 (liftPara K) (liftPara L)
  liftCell α = mkReparameterization
    (mapParameters α)
    (lift-preserves α)

  liftCell-id :
    liftCell (id₂ {F = K}) ≈ id₂ {F = liftPara K}
  liftCell-id = M.Equiv.refl

  liftCell-compose :
    (β : Reparameterization 𝒜 L N) →
    (α : Reparameterization 𝒜 K L) →
    liftCell (β ∘ᵥ α) ≈ (liftCell β ∘ᵥ liftCell α)
  liftCell-compose β α = M.Equiv.refl

  liftCell-resp-≈ :
    {α β : Reparameterization 𝒜 K L} →
    α ≈ β → liftCell α ≈ liftCell β
  liftCell-resp-≈ α≈β = α≈β

  liftHom : (A B : 𝒞.Obj) →
    Functor
      (Hom 𝒜 A B)
      (Hom 𝒜 (S.F.F₀ A) (S.F.F₀ B))
  liftHom A B = record
    { F₀ = λ K → liftPara K
    ; F₁ = λ α → liftCell α
    ; identity = λ {A = K} → liftCell-id {K = K}
    ; homomorphism = λ {f = α} {g = β} →
        liftCell-compose β α
    ; F-resp-≈ = λ α≈β → α≈β
    }

  -- AS2 and joint naturality identify lifting after Para composition with
  -- composing the lifted parameterized maps.
  lift-composition-run :
    ∀ {A B D : 𝒞.Obj} →
    (L : Para 𝒜 B D) →
    (K : Para 𝒜 A B) →
    run (liftPara (L ∘ₚ K))
      𝒞.≈
    run (liftPara L ∘ₚ liftPara K)
  lift-composition-run {A = A} {B = B} L K = begin
    S.F.F₁
      (run L 𝒞.∘
        ((M.id 𝒜.⊙₁ run K) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , A))) 𝒞.∘
      S.σ (Parameters L V.⊗₀ Parameters K) A
      ≈⟨ S.F.homomorphism ⟩∘⟨refl ⟩
    (S.F.F₁ (run L) 𝒞.∘
      S.F.F₁
        ((M.id 𝒜.⊙₁ run K) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , A))) 𝒞.∘
      S.σ (Parameters L V.⊗₀ Parameters K) A
      ≈⟨ 𝒞.assoc ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.F.F₁
        ((M.id 𝒜.⊙₁ run K) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , A)) 𝒞.∘
        S.σ (Parameters L V.⊗₀ Parameters K) A)
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
        (S.F.homomorphism ⟩∘⟨refl) ⟩
    S.F.F₁ (run L) 𝒞.∘
      (((S.F.F₁ (M.id 𝒜.⊙₁ run K)) 𝒞.∘
        S.F.F₁
          (𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , A))) 𝒞.∘
        S.σ (Parameters L V.⊗₀ Parameters K) A)
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.F.F₁ (M.id 𝒜.⊙₁ run K) 𝒞.∘
        (S.F.F₁
          (𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , A)) 𝒞.∘
          S.σ (Parameters L V.⊗₀ Parameters K) A))
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
        (𝒞.Equiv.refl ⟩∘⟨ S.associativity-coherence) ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.F.F₁ (M.id 𝒜.⊙₁ run K) 𝒞.∘
        (S.σ (Parameters L) (Parameters K 𝒜.⊙₀ A) 𝒞.∘
          ((M.id 𝒜.⊙₁ S.σ (Parameters K) A) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters L , Parameters K) , S.F.F₀ A))))
      ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
    S.F.F₁ (run L) 𝒞.∘
      ((S.F.F₁ (M.id 𝒜.⊙₁ run K) 𝒞.∘
        S.σ (Parameters L) (Parameters K 𝒜.⊙₀ A)) 𝒞.∘
        ((M.id 𝒜.⊙₁ S.σ (Parameters K) A) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , S.F.F₀ A)))
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
        (S.strengthen.sym-commute (M.id , run K) ⟩∘⟨refl) ⟩
    S.F.F₁ (run L) 𝒞.∘
      ((S.σ (Parameters L) B 𝒞.∘
        (M.id 𝒜.⊙₁ S.F.F₁ (run K))) 𝒞.∘
        ((M.id 𝒜.⊙₁ S.σ (Parameters K) A) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , S.F.F₀ A)))
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.σ (Parameters L) B 𝒞.∘
        ((M.id 𝒜.⊙₁ S.F.F₁ (run K)) 𝒞.∘
          ((M.id 𝒜.⊙₁ S.σ (Parameters K) A) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters L , Parameters K) , S.F.F₀ A))))
      ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨
        (𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc) ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.σ (Parameters L) B 𝒞.∘
        (((M.id 𝒜.⊙₁ S.F.F₁ (run K)) 𝒞.∘
          (M.id 𝒜.⊙₁ S.σ (Parameters K) A)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , S.F.F₀ A)))
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
        (𝒞.Equiv.refl ⟩∘⟨
          (merge-fixed-action
            {𝒜 = 𝒜} {P = Parameters L}
            (S.F.F₁ (run K))
            (S.σ (Parameters K) A) ⟩∘⟨refl)) ⟩
    S.F.F₁ (run L) 𝒞.∘
      (S.σ (Parameters L) B 𝒞.∘
        ((M.id 𝒜.⊙₁ run (liftPara K)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters L , Parameters K) , S.F.F₀ A)))
      ≈˘⟨ 𝒞.assoc ⟩
    run (liftPara L) 𝒞.∘
      ((M.id 𝒜.⊙₁ run (liftPara K)) 𝒞.∘
        𝒜.associator.⇒.η
          ((Parameters L , Parameters K) , S.F.F₀ A))
      ∎
    where
      open 𝒞.HomReasoning

  lift-identity-run :
    ∀ {A : 𝒞.Obj} →
    run (liftPara (idₚ {𝒜 = 𝒜} {A = A}))
      𝒞.≈
    run (idₚ {𝒜 = 𝒜} {A = S.F.F₀ A})
  lift-identity-run = S.unit-coherence

  identity-comparison :
    ∀ {A : 𝒞.Obj} →
    Reparameterization 𝒜
      (idₚ {𝒜 = 𝒜} {A = S.F.F₀ A})
      (liftPara (idₚ {𝒜 = 𝒜} {A = A}))
  identity-comparison =
    mkReparameterization M.id proof
    where
      open 𝒞.HomReasoning
      proof =
        lift-identity-run ○
        identityPreserves
          {𝒜 = 𝒜}
          {F = idₚ {𝒜 = 𝒜} {A = S.F.F₀ _}}

  identity-comparison⁻¹ :
    ∀ {A : 𝒞.Obj} →
    Reparameterization 𝒜
      (liftPara (idₚ {𝒜 = 𝒜} {A = A}))
      (idₚ {𝒜 = 𝒜} {A = S.F.F₀ A})
  identity-comparison⁻¹ =
    mkReparameterization M.id proof
    where
      open 𝒞.HomReasoning
      proof =
        𝒞.Equiv.sym lift-identity-run ○
        identityPreserves
          {𝒜 = 𝒜}
          {F = liftPara (idₚ {𝒜 = 𝒜})}

  composition-comparison :
    ∀ {A B D : 𝒞.Obj}
      (L : Para 𝒜 B D)
      (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (liftPara L ∘ₚ liftPara K)
      (liftPara (L ∘ₚ K))
  composition-comparison L K =
    mkReparameterization M.id proof
    where
      open 𝒞.HomReasoning
      proof =
        lift-composition-run L K ○
        identityPreserves {𝒜 = 𝒜} {F = liftPara L ∘ₚ liftPara K}

  composition-comparison⁻¹ :
    ∀ {A B D : 𝒞.Obj}
      (L : Para 𝒜 B D)
      (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (liftPara (L ∘ₚ K))
      (liftPara L ∘ₚ liftPara K)
  composition-comparison⁻¹ L K =
    mkReparameterization M.id proof
    where
      open 𝒞.HomReasoning
      proof =
        𝒞.Equiv.sym (lift-composition-run L K) ○
        identityPreserves {𝒜 = 𝒜} {F = liftPara (L ∘ₚ K)}

  lift-restriction-run :
    ∀ {A B : 𝒞.Obj}
      (K : Para 𝒜 A B)
      {Q : M.Obj}
      (r : Q M.⇒ Parameters K) →
    run (liftPara (restrictParameters K r))
      𝒞.≈
    run (restrictParameters (liftPara K) r)
  lift-restriction-run K r =
    preserves-run (liftCell (restrictCell K r))

  -- Pairwise comonoid sharing is restriction along copyParameter, so the
  -- general restriction theorem specializes without stronger assumptions.
  lift-sharing-run :
    ∀ {A B : 𝒞.Obj} {P : M.Obj}
      (C : ParameterComonoid V P)
      (f : ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    run
      (liftPara
        (tieParameterPair
          {𝒜 = 𝒜} {A = A} {B = B} C f))
      𝒞.≈
    run
      (tieParameterPair
        {𝒜 = 𝒜} {A = S.F.F₀ A} {B = S.F.F₀ B} C
        (run
          (liftPara
            (untiedParameterPair
              {𝒜 = 𝒜} {A = A} {B = B} P f))))
  lift-sharing-run {A = A} {B = B} {P = P} C f =
    lift-restriction-run
      (untiedParameterPair {𝒜 = 𝒜} {A = A} {B = B} P f)
      (copyParameter C)

  private
    id-commute :
      ∀ {P Q : M.Obj} {r : P M.⇒ Q} →
      (r M.∘ M.id) M.≈ (M.id M.∘ r)
    id-commute =
      M.identityʳ ○ M.Equiv.sym M.identityˡ
      where
        open M.HomReasoning

    unitaryˡ-coherence :
      ∀ {A B : 𝒞.Obj} {K : Para 𝒜 A B} →
      ((((M.id V.⊗₁ M.id) M.∘ M.id) M.∘
        V.unitorˡ.to {X = Parameters K}))
        M.≈
      V.unitorˡ.to
    unitaryˡ-coherence = begin
      ((M.id V.⊗₁ M.id) M.∘ M.id) M.∘ V.unitorˡ.to
        ≈⟨ M.∘-resp-≈ˡ
          (M.∘-resp-≈ˡ V.⊗.identity ○ M.identity²) ⟩
      M.id M.∘ V.unitorˡ.to
        ≈⟨ M.identityˡ ⟩
      V.unitorˡ.to
        ∎
      where
        open M.HomReasoning

    unitaryʳ-coherence :
      ∀ {A B : 𝒞.Obj} {K : Para 𝒜 A B} →
      ((((M.id V.⊗₁ M.id) M.∘ M.id) M.∘
        V.unitorʳ.to {X = Parameters K}))
        M.≈
      V.unitorʳ.to
    unitaryʳ-coherence = begin
      ((M.id V.⊗₁ M.id) M.∘ M.id) M.∘ V.unitorʳ.to
        ≈⟨ M.∘-resp-≈ˡ
          (M.∘-resp-≈ˡ V.⊗.identity ○ M.identity²) ⟩
      M.id M.∘ V.unitorʳ.to
        ≈⟨ M.identityˡ ⟩
      V.unitorʳ.to
        ∎
      where
        open M.HomReasoning

    associativity-coherence :
      ∀ {A B D E : 𝒞.Obj}
        {K : Para 𝒜 A B}
        {L : Para 𝒜 B D}
        {N : Para 𝒜 D E} →
      ((((M.id V.⊗₁ M.id) M.∘ M.id) M.∘
        V.associator.to
          {X = Parameters N}
          {Y = Parameters L}
          {Z = Parameters K}))
        M.≈
      ((V.associator.to M.∘ (M.id V.⊗₁ M.id))
        M.∘ M.id)
    associativity-coherence = begin
      ((M.id V.⊗₁ M.id) M.∘ M.id) M.∘ V.associator.to
        ≈⟨ M.∘-resp-≈ˡ
          (M.∘-resp-≈ˡ V.⊗.identity ○ M.identity²) ⟩
      M.id M.∘ V.associator.to
        ≈⟨ M.identityˡ ⟩
      V.associator.to
        ≈˘⟨ M.∘-resp-≈ʳ V.⊗.identity
          ○ M.identityʳ ⟩
      V.associator.to M.∘ (M.id V.⊗₁ M.id)
        ≈˘⟨ M.identityʳ ⟩
      (V.associator.to M.∘ (M.id V.⊗₁ M.id))
        M.∘ M.id
        ∎
      where
        open M.HomReasoning

  -- The comparison cells have identity parameter maps. Consequently the
  -- pseudofunctor coherence laws reduce to equations in M; evaluator proof
  -- fields are intentionally not observed by hom-category equality.
  liftPseudofunctor :
    Pseudofunctor (ParaActegory 𝒜) (ParaActegory 𝒜)
  liftPseudofunctor = record
    { P₀ = S.F.F₀
    ; P₁ = λ {A} {B} → liftHom A B
    ; P-identity = niHelper record
        { η = λ _ → identity-comparison
        ; η⁻¹ = λ _ → identity-comparison⁻¹
        ; commute = λ _ → id-commute
        ; iso = λ _ → record
            { isoˡ = M.identity²
            ; isoʳ = M.identity²
            }
        }
    ; P-homomorphism = niHelper record
        { η = λ where
            (L , K) → composition-comparison L K
        ; η⁻¹ = λ where
            (L , K) → composition-comparison⁻¹ L K
        ; commute = λ _ → id-commute
        ; iso = λ _ → record
            { isoˡ = M.identity²
            ; isoʳ = M.identity²
            }
        }
    ; unitaryˡ = λ {f = K} → unitaryˡ-coherence {K = K}
    ; unitaryʳ = λ {f = K} → unitaryʳ-coherence {K = K}
    ; assoc = λ {f = K} {g = L} {h = N} →
        associativity-coherence {K = K} {L = L} {N = N}
    }
