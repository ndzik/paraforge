{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Strong.Monad where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Pseudofunctor using (Pseudofunctor)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Actegory.Strong.Monad
  using (StrongMonad; strongEndofunctor)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Laws
  using
    ( unitorˡ-preserves; unitorʳ⁻¹-preserves
    ; forward-from-inverse; merge-fixed-action
    )
open import ParaForge.Para.Actegory.Bicategory using (ParaActegory)
import ParaForge.Para.Actegory.Strong.Endofunctor as EndofunctorLift

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

module _
  {M : Category oₘ ℓₘ eₘ}
  {𝒞 : Category o𝒞 ℓ𝒞 e𝒞}
  {V : Monoidal M}
  {𝒜 : Actegory V 𝒞}
  (S : StrongMonad 𝒜) where

  private
    module M = Category M
    module 𝒞 = Category 𝒞
    module V = Monoidal V
    module 𝒜 = Actegory 𝒜
    module S = StrongMonad S

  private
    variable
      A B : 𝒞.Obj

  underlyingPseudofunctor :
    Pseudofunctor (ParaActegory 𝒜) (ParaActegory 𝒜)
  underlyingPseudofunctor =
    EndofunctorLift.liftPseudofunctor (strongEndofunctor S)

  -- The paper writes these components as (I , η) and (I , μ) under
  -- strictness. In a weak actegory their evaluators must first eliminate the
  -- action of I.
  unitPara : (A : 𝒞.Obj) → Para 𝒜 A (S.monad.F.F₀ A)
  unitPara A = mkPara V.unit
    (S.monad.η.η A 𝒞.∘ 𝒜.unitor.⇒.η A)

  multiplicationPara :
    (A : 𝒞.Obj) →
    Para 𝒜 (S.monad.F.F₀ (S.monad.F.F₀ A)) (S.monad.F.F₀ A)
  multiplicationPara A = mkPara V.unit
    (S.monad.μ.η A 𝒞.∘
      𝒜.unitor.⇒.η (S.monad.F.F₀ (S.monad.F.F₀ A)))

  -- No braiding is needed to exchange P with the tensor unit. The canonical
  -- map is built solely from the right and left unitors.
  unitSwap : (P : M.Obj) →
    (P V.⊗₀ V.unit) M.⇒ (V.unit V.⊗₀ P)
  unitSwap P = V.unitorˡ.to M.∘ V.unitorʳ.from

  unitSwap⁻¹ : (P : M.Obj) →
    (V.unit V.⊗₀ P) M.⇒ (P V.⊗₀ V.unit)
  unitSwap⁻¹ P = V.unitorʳ.to M.∘ V.unitorˡ.from

  unitSwap-isoˡ : ∀ {P : M.Obj} →
    (unitSwap P M.∘ unitSwap⁻¹ P) M.≈ M.id
  unitSwap-isoˡ {P = P} = begin
    (V.unitorˡ.to M.∘ V.unitorʳ.from) M.∘
      (V.unitorʳ.to M.∘ V.unitorˡ.from)
      ≈⟨ M.assoc ⟩
    V.unitorˡ.to M.∘
      (V.unitorʳ.from M.∘
        (V.unitorʳ.to M.∘ V.unitorˡ.from))
      ≈˘⟨ M.Equiv.refl ⟩∘⟨ M.assoc ⟩
    V.unitorˡ.to M.∘
      ((V.unitorʳ.from M.∘ V.unitorʳ.to) M.∘
        V.unitorˡ.from)
      ≈⟨ M.Equiv.refl ⟩∘⟨
        (V.unitorʳ.isoʳ ⟩∘⟨refl) ⟩
    V.unitorˡ.to M.∘ (M.id M.∘ V.unitorˡ.from)
      ≈⟨ M.Equiv.refl ⟩∘⟨ M.identityˡ ⟩
    V.unitorˡ.to M.∘ V.unitorˡ.from
      ≈⟨ V.unitorˡ.isoˡ ⟩
    M.id
      ∎
    where
      open M.HomReasoning

  unitSwap-natural :
    ∀ {P Q : M.Obj} (r : Q M.⇒ P) →
    ((M.id V.⊗₁ r) M.∘ unitSwap Q)
      M.≈
    (unitSwap P M.∘ (r V.⊗₁ M.id))
  unitSwap-natural {P = P} {Q = Q} r = begin
    (M.id V.⊗₁ r) M.∘
      (V.unitorˡ.to M.∘ V.unitorʳ.from)
      ≈˘⟨ M.assoc ⟩
    ((M.id V.⊗₁ r) M.∘ V.unitorˡ.to) M.∘
      V.unitorʳ.from
      ≈⟨ M.Equiv.sym V.unitorˡ-commute-to ⟩∘⟨refl ⟩
    (V.unitorˡ.to M.∘ r) M.∘ V.unitorʳ.from
      ≈⟨ M.assoc ⟩
    V.unitorˡ.to M.∘ (r M.∘ V.unitorʳ.from)
      ≈⟨ M.Equiv.refl ⟩∘⟨
        M.Equiv.sym V.unitorʳ-commute-from ⟩
    V.unitorˡ.to M.∘
      (V.unitorʳ.from M.∘ (r V.⊗₁ M.id))
      ≈˘⟨ M.assoc ⟩
    (V.unitorˡ.to M.∘ V.unitorʳ.from) M.∘
      (r V.⊗₁ M.id)
      ∎
    where
      open M.HomReasoning

  unitSwap-isoʳ : ∀ {P : M.Obj} →
    (unitSwap⁻¹ P M.∘ unitSwap P) M.≈ M.id
  unitSwap-isoʳ {P = P} = begin
    (V.unitorʳ.to M.∘ V.unitorˡ.from) M.∘
      (V.unitorˡ.to M.∘ V.unitorʳ.from)
      ≈⟨ M.assoc ⟩
    V.unitorʳ.to M.∘
      (V.unitorˡ.from M.∘
        (V.unitorˡ.to M.∘ V.unitorʳ.from))
      ≈˘⟨ M.Equiv.refl ⟩∘⟨ M.assoc ⟩
    V.unitorʳ.to M.∘
      ((V.unitorˡ.from M.∘ V.unitorˡ.to) M.∘
        V.unitorʳ.from)
      ≈⟨ M.Equiv.refl ⟩∘⟨
        (V.unitorˡ.isoʳ ⟩∘⟨refl) ⟩
    V.unitorʳ.to M.∘ (M.id M.∘ V.unitorʳ.from)
      ≈⟨ M.Equiv.refl ⟩∘⟨ M.identityˡ ⟩
    V.unitorʳ.to M.∘ V.unitorʳ.from
      ≈⟨ V.unitorʳ.isoˡ ⟩
    M.id
      ∎
    where
      open M.HomReasoning

  private
    unitOnPara : (K : Para 𝒜 A B) →
      Para 𝒜 A (S.monad.F.F₀ B)
    unitOnPara {B = B} K = mkPara (Parameters K)
      (S.monad.η.η B 𝒞.∘ run K)

    unit-compose-run : (K : Para 𝒜 A B) →
      run (unitPara B ∘ₚ K)
        𝒞.≈
      (S.monad.η.η B 𝒞.∘
        run (idₚ {𝒜 = 𝒜} ∘ₚ K))
    unit-compose-run {B = B} K = 𝒞.assoc

    unit-left-normalization : (K : Para 𝒜 A B) →
      Reparameterization 𝒜
        (unitPara B ∘ₚ K)
        (unitOnPara K)
    unit-left-normalization {B = B} K =
      mkReparameterization V.unitorˡ.to proof
      where
        open 𝒞.HomReasoning
        proof = begin
          run (unitOnPara K)
            ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
              unitorˡ-preserves {𝒜 = 𝒜} {F = K} ⟩
          S.monad.η.η B 𝒞.∘
            (run (idₚ ∘ₚ K) 𝒞.∘
              (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id))
            ≈˘⟨ 𝒞.assoc ⟩
          (S.monad.η.η B 𝒞.∘ run (idₚ ∘ₚ K)) 𝒞.∘
            (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ≈˘⟨ unit-compose-run K ⟩∘⟨refl ⟩
          run (unitPara B ∘ₚ K) 𝒞.∘
            (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ∎

    unit-right-run : (K : Para 𝒜 A B) →
      run
        (EndofunctorLift.liftPara (strongEndofunctor S) K
          ∘ₚ unitPara A)
        𝒞.≈
      run (unitOnPara K ∘ₚ idₚ)
    unit-right-run {A = A} {B = B} K = begin
      (S.monad.F.F₁ (run K) 𝒞.∘
        S.σ (Parameters K) A) 𝒞.∘
        ((M.id 𝒜.⊙₁
          (S.monad.η.η A 𝒞.∘ 𝒜.unitor.⇒.η A)) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters K , V.unit) , A))
        ≈⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          ((M.id 𝒜.⊙₁
            (S.monad.η.η A 𝒞.∘ 𝒜.unitor.⇒.η A)) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) , A)))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.refl ⟩∘⟨
            (𝒜.action.F-resp-≈
              (M.Equiv.sym M.identity² , 𝒞.Equiv.refl)
              ○ 𝒜.action.homomorphism)
            ⟩∘⟨refl) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          (((M.id 𝒜.⊙₁ S.monad.η.η A) 𝒞.∘
            (M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A)) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) , A)))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          ((M.id 𝒜.⊙₁ S.monad.η.η A) 𝒞.∘
            ((M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A) 𝒞.∘
              𝒜.associator.⇒.η
                ((Parameters K , V.unit) , A))))
        ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        ((S.σ (Parameters K) A 𝒞.∘
          (M.id 𝒜.⊙₁ S.monad.η.η A)) 𝒞.∘
          ((M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) , A)))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (S.monad-unit-coherence ⟩∘⟨refl) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.monad.η.η (Parameters K 𝒜.⊙₀ A) 𝒞.∘
          ((M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) , A)))
        ≈˘⟨ 𝒞.assoc ⟩
      (S.monad.F.F₁ (run K) 𝒞.∘
        S.monad.η.η (Parameters K 𝒜.⊙₀ A)) 𝒞.∘
          ((M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) , A))
        ≈⟨ S.monad.η.sym-commute (run K) ⟩∘⟨refl ⟩
      (S.monad.η.η B 𝒞.∘ run K) 𝒞.∘
        ((M.id 𝒜.⊙₁ 𝒜.unitor.⇒.η A) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters K , V.unit) , A))
        ∎
      where
        open 𝒞.HomReasoning

    unit-right-normalization : (K : Para 𝒜 A B) →
      Reparameterization 𝒜
        (unitOnPara K)
        (EndofunctorLift.liftPara (strongEndofunctor S) K
          ∘ₚ unitPara A)
    unit-right-normalization K =
      mkReparameterization V.unitorʳ.from
        (unit-right-run K ○
          unitorʳ⁻¹-preserves {𝒜 = 𝒜} {F = unitOnPara K})
      where
        open 𝒞.HomReasoning

  -- Pseudonaturality is oriented αB ∘ K ⇒ T(K) ∘ αA, matching
  -- Definition G.1's target-to-source parameter maps.
  unitNaturality : (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (unitPara B ∘ₚ K)
      (EndofunctorLift.liftPara (strongEndofunctor S) K
        ∘ₚ unitPara A)
  unitNaturality K =
    unit-right-normalization K ∘ᵥ unit-left-normalization K

  unitNaturality-map : (K : Para 𝒜 A B) →
    mapParameters (unitNaturality K) M.≈
      unitSwap (Parameters K)
  unitNaturality-map K = M.Equiv.refl

  unitNaturality⁻¹ : (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (EndofunctorLift.liftPara (strongEndofunctor S) K
        ∘ₚ unitPara A)
      (unitPara B ∘ₚ K)
  unitNaturality⁻¹ K =
    mkReparameterization (unitSwap⁻¹ (Parameters K))
      (forward-from-inverse
        {𝒜 = 𝒜}
        (unitSwap-isoˡ {P = Parameters K})
        (preserves-run (unitNaturality K)))

  unitNaturality-isoˡ : (K : Para 𝒜 A B) →
    (unitNaturality⁻¹ K ∘ᵥ unitNaturality K)
      ≈ id₂
  unitNaturality-isoˡ K = unitSwap-isoˡ

  unitNaturality-isoʳ : (K : Para 𝒜 A B) →
    (unitNaturality K ∘ᵥ unitNaturality⁻¹ K)
      ≈ id₂
  unitNaturality-isoʳ K = unitSwap-isoʳ

  private
    lift₁ : Para 𝒜 A B →
      Para 𝒜 (S.monad.F.F₀ A) (S.monad.F.F₀ B)
    lift₁ = EndofunctorLift.liftPara (strongEndofunctor S)

    lift₂ : Para 𝒜 A B →
      Para 𝒜
        (S.monad.F.F₀ (S.monad.F.F₀ A))
        (S.monad.F.F₀ (S.monad.F.F₀ B))
    lift₂ K = lift₁ (lift₁ K)

    multiplicationOnPara : (K : Para 𝒜 A B) →
      Para 𝒜
        (S.monad.F.F₀ (S.monad.F.F₀ A))
        (S.monad.F.F₀ B)
    multiplicationOnPara {B = B} K =
      mkPara (Parameters K)
        (S.monad.μ.η B 𝒞.∘ run (lift₂ K))

    multiplication-compose-run : (K : Para 𝒜 A B) →
      run (multiplicationPara B ∘ₚ lift₂ K)
        𝒞.≈
      (S.monad.μ.η B 𝒞.∘
        run (idₚ {𝒜 = 𝒜} ∘ₚ lift₂ K))
    multiplication-compose-run {B = B} K = 𝒞.assoc

    multiplication-left-normalization : (K : Para 𝒜 A B) →
      Reparameterization 𝒜
        (multiplicationPara B ∘ₚ lift₂ K)
        (multiplicationOnPara K)
    multiplication-left-normalization {B = B} K =
      mkReparameterization V.unitorˡ.to proof
      where
        open 𝒞.HomReasoning
        proof = begin
          run (multiplicationOnPara K)
            ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
              unitorˡ-preserves {𝒜 = 𝒜} {F = lift₂ K} ⟩
          S.monad.μ.η B 𝒞.∘
            (run (idₚ ∘ₚ lift₂ K) 𝒞.∘
              (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id))
            ≈˘⟨ 𝒞.assoc ⟩
          (S.monad.μ.η B 𝒞.∘
            run (idₚ ∘ₚ lift₂ K)) 𝒞.∘
              (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ≈˘⟨ multiplication-compose-run K ⟩∘⟨refl ⟩
          run (multiplicationPara B ∘ₚ lift₂ K) 𝒞.∘
            (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ∎

    multiplication-right-run : (K : Para 𝒜 A B) →
      run (lift₁ K ∘ₚ multiplicationPara A)
        𝒞.≈
      run (multiplicationOnPara K ∘ₚ idₚ)
    multiplication-right-run {A = A} {B = B} K = begin
      (S.monad.F.F₁ (run K) 𝒞.∘
        S.σ (Parameters K) A) 𝒞.∘
        ((M.id 𝒜.⊙₁
          (S.monad.μ.η A 𝒞.∘
            𝒜.unitor.⇒.η
              (S.monad.F.F₀ (S.monad.F.F₀ A)))) 𝒞.∘
          𝒜.associator.⇒.η
            ((Parameters K , V.unit) ,
              S.monad.F.F₀ (S.monad.F.F₀ A)))
        ≈⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          ((M.id 𝒜.⊙₁
            (S.monad.μ.η A 𝒞.∘
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A)))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A))))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.refl ⟩∘⟨
            (𝒜.action.F-resp-≈
              (M.Equiv.sym M.identity² , 𝒞.Equiv.refl)
              ○ 𝒜.action.homomorphism)
            ⟩∘⟨refl) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          (((M.id 𝒜.⊙₁ S.monad.μ.η A) 𝒞.∘
            (M.id 𝒜.⊙₁
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A)))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A))))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.σ (Parameters K) A 𝒞.∘
          ((M.id 𝒜.⊙₁ S.monad.μ.η A) 𝒞.∘
            ((M.id 𝒜.⊙₁
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
              𝒜.associator.⇒.η
                ((Parameters K , V.unit) ,
                  S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        ((S.σ (Parameters K) A 𝒞.∘
          (M.id 𝒜.⊙₁ S.monad.μ.η A)) 𝒞.∘
          ((M.id 𝒜.⊙₁
            𝒜.unitor.⇒.η
              (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A))))
        ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨
          (S.multiplication-coherence ⟩∘⟨refl) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        ((S.monad.μ.η (Parameters K 𝒜.⊙₀ A) 𝒞.∘
          (S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            S.σ (Parameters K) (S.monad.F.F₀ A))) 𝒞.∘
          ((M.id 𝒜.⊙₁
            𝒜.unitor.⇒.η
              (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A))))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.monad.μ.η (Parameters K 𝒜.⊙₀ A) 𝒞.∘
          ((S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            S.σ (Parameters K) (S.monad.F.F₀ A)) 𝒞.∘
            ((M.id 𝒜.⊙₁
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
              𝒜.associator.⇒.η
                ((Parameters K , V.unit) ,
                  S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc) ⟩
      S.monad.F.F₁ (run K) 𝒞.∘
        (S.monad.μ.η (Parameters K 𝒜.⊙₀ A) 𝒞.∘
          (S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
              ((M.id 𝒜.⊙₁
                𝒜.unitor.⇒.η
                  (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
                𝒜.associator.⇒.η
                  ((Parameters K , V.unit) ,
                    S.monad.F.F₀ (S.monad.F.F₀ A))))))
        ≈˘⟨ 𝒞.assoc ⟩
      (S.monad.F.F₁ (run K) 𝒞.∘
        S.monad.μ.η (Parameters K 𝒜.⊙₀ A)) 𝒞.∘
          (S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
              ((M.id 𝒜.⊙₁
                𝒜.unitor.⇒.η
                  (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
                𝒜.associator.⇒.η
                  ((Parameters K , V.unit) ,
                    S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈˘⟨ S.monad.μ.commute (run K) ⟩∘⟨refl ⟩
      (S.monad.μ.η B 𝒞.∘
        S.monad.F.F₁ (S.monad.F.F₁ (run K))) 𝒞.∘
          (S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
              ((M.id 𝒜.⊙₁
                𝒜.unitor.⇒.η
                  (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
                𝒜.associator.⇒.η
                  ((Parameters K , V.unit) ,
                    S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈⟨ 𝒞.assoc ⟩
      S.monad.μ.η B 𝒞.∘
        (S.monad.F.F₁ (S.monad.F.F₁ (run K)) 𝒞.∘
          (S.monad.F.F₁ (S.σ (Parameters K) A) 𝒞.∘
            (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
              ((M.id 𝒜.⊙₁
                𝒜.unitor.⇒.η
                  (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
                𝒜.associator.⇒.η
                  ((Parameters K , V.unit) ,
                    S.monad.F.F₀ (S.monad.F.F₀ A))))))
        ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
      S.monad.μ.η B 𝒞.∘
        ((S.monad.F.F₁ (S.monad.F.F₁ (run K)) 𝒞.∘
          S.monad.F.F₁ (S.σ (Parameters K) A)) 𝒞.∘
          (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
            ((M.id 𝒜.⊙₁
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
              𝒜.associator.⇒.η
                ((Parameters K , V.unit) ,
                  S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
          (𝒞.Equiv.sym S.monad.F.homomorphism ⟩∘⟨refl) ⟩
      S.monad.μ.η B 𝒞.∘
        (S.monad.F.F₁
          (S.monad.F.F₁ (run K) 𝒞.∘
            S.σ (Parameters K) A) 𝒞.∘
          (S.σ (Parameters K) (S.monad.F.F₀ A) 𝒞.∘
            ((M.id 𝒜.⊙₁
              𝒜.unitor.⇒.η
                (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
              𝒜.associator.⇒.η
                ((Parameters K , V.unit) ,
                  S.monad.F.F₀ (S.monad.F.F₀ A)))))
        ≈˘⟨ 𝒞.Equiv.refl ⟩∘⟨ 𝒞.assoc ⟩
      S.monad.μ.η B 𝒞.∘
        ((S.monad.F.F₁
          (S.monad.F.F₁ (run K) 𝒞.∘
            S.σ (Parameters K) A) 𝒞.∘
          S.σ (Parameters K) (S.monad.F.F₀ A)) 𝒞.∘
          ((M.id 𝒜.⊙₁
            𝒜.unitor.⇒.η
              (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A))))
        ≈˘⟨ 𝒞.assoc ⟩
      (S.monad.μ.η B 𝒞.∘
        (S.monad.F.F₁
          (S.monad.F.F₁ (run K) 𝒞.∘
            S.σ (Parameters K) A) 𝒞.∘
          S.σ (Parameters K) (S.monad.F.F₀ A))) 𝒞.∘
          ((M.id 𝒜.⊙₁
            𝒜.unitor.⇒.η
              (S.monad.F.F₀ (S.monad.F.F₀ A))) 𝒞.∘
            𝒜.associator.⇒.η
              ((Parameters K , V.unit) ,
                S.monad.F.F₀ (S.monad.F.F₀ A)))
        ∎
      where
        open 𝒞.HomReasoning

    multiplication-right-normalization : (K : Para 𝒜 A B) →
      Reparameterization 𝒜
        (multiplicationOnPara K)
        (lift₁ K ∘ₚ multiplicationPara A)
    multiplication-right-normalization K =
      mkReparameterization V.unitorʳ.from
        (multiplication-right-run K ○
          unitorʳ⁻¹-preserves
            {𝒜 = 𝒜} {F = multiplicationOnPara K})
      where
        open 𝒞.HomReasoning

  multiplicationNaturality : (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (multiplicationPara B ∘ₚ lift₂ K)
      (lift₁ K ∘ₚ multiplicationPara A)
  multiplicationNaturality K =
    multiplication-right-normalization K ∘ᵥ
      multiplication-left-normalization K

  multiplicationNaturality-map : (K : Para 𝒜 A B) →
    mapParameters (multiplicationNaturality K) M.≈
      unitSwap (Parameters K)
  multiplicationNaturality-map K = M.Equiv.refl

  multiplicationNaturality⁻¹ : (K : Para 𝒜 A B) →
    Reparameterization 𝒜
      (lift₁ K ∘ₚ multiplicationPara A)
      (multiplicationPara B ∘ₚ lift₂ K)
  multiplicationNaturality⁻¹ K =
    mkReparameterization (unitSwap⁻¹ (Parameters K))
      (forward-from-inverse
        {𝒜 = 𝒜}
        (unitSwap-isoˡ {P = Parameters K})
        (preserves-run (multiplicationNaturality K)))

  multiplicationNaturality-isoˡ : (K : Para 𝒜 A B) →
    (multiplicationNaturality⁻¹ K ∘ᵥ
      multiplicationNaturality K)
      ≈ id₂
  multiplicationNaturality-isoˡ K = unitSwap-isoˡ

  multiplicationNaturality-isoʳ : (K : Para 𝒜 A B) →
    (multiplicationNaturality K ∘ᵥ
      multiplicationNaturality⁻¹ K)
      ≈ id₂
  multiplicationNaturality-isoʳ K = unitSwap-isoʳ

  private
    variable
      X Y Z : 𝒞.Obj

    parameterFree : (X 𝒞.⇒ Y) → Para 𝒜 X Y
    parameterFree {X = X} f = mkPara V.unit
      (f 𝒞.∘ 𝒜.unitor.⇒.η X)

    parameterFree-compose :
      (g : Y 𝒞.⇒ Z) (f : X 𝒞.⇒ Y) →
      Reparameterization 𝒜
        (parameterFree g ∘ₚ parameterFree f)
        (parameterFree (g 𝒞.∘ f))
    parameterFree-compose {X = X} g f =
      mkReparameterization V.unitorˡ.to proof
      where
        open 𝒞.HomReasoning
        postcompose-run :
          run (parameterFree g ∘ₚ parameterFree f)
            𝒞.≈
          (g 𝒞.∘ run (idₚ {𝒜 = 𝒜} ∘ₚ parameterFree f))
        postcompose-run = 𝒞.assoc

        proof = begin
          run (parameterFree (g 𝒞.∘ f))
            ≈⟨ 𝒞.assoc ⟩
          g 𝒞.∘ (f 𝒞.∘ 𝒜.unitor.⇒.η X)
            ≈⟨ 𝒞.Equiv.refl ⟩∘⟨
              unitorˡ-preserves
                {𝒜 = 𝒜} {F = parameterFree f} ⟩
          g 𝒞.∘
            (run (idₚ ∘ₚ parameterFree f) 𝒞.∘
              (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id))
            ≈˘⟨ 𝒞.assoc ⟩
          (g 𝒞.∘ run (idₚ ∘ₚ parameterFree f)) 𝒞.∘
            (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ≈˘⟨ postcompose-run ⟩∘⟨refl ⟩
          run (parameterFree g ∘ₚ parameterFree f) 𝒞.∘
            (V.unitorˡ.to 𝒜.⊙₁ 𝒞.id)
            ∎

    parameterFree-compose⁻¹ :
      (g : Y 𝒞.⇒ Z) (f : X 𝒞.⇒ Y) →
      Reparameterization 𝒜
        (parameterFree (g 𝒞.∘ f))
        (parameterFree g ∘ₚ parameterFree f)
    parameterFree-compose⁻¹ g f =
      mkReparameterization V.unitorˡ.from
        (forward-from-inverse
          {𝒜 = 𝒜}
          V.unitorˡ.isoˡ
          (preserves-run (parameterFree-compose g f)))

    parameterFree-cell :
      {f g : X 𝒞.⇒ Y} →
      f 𝒞.≈ g →
      Reparameterization 𝒜 (parameterFree f) (parameterFree g)
    parameterFree-cell {f = f} {g = g} f≈g =
      mkReparameterization M.id
        ((𝒞.Equiv.sym f≈g ⟩∘⟨refl) ○
          identityPreserves {𝒜 = 𝒜} {F = parameterFree f})
      where
        open 𝒞.HomReasoning

    lift-parameterFree-run : (f : X 𝒞.⇒ Y) →
      run (lift₁ (parameterFree f))
        𝒞.≈
      run (parameterFree (S.monad.F.F₁ f))
    lift-parameterFree-run {X = X} {Y = Y} f = begin
      S.monad.F.F₁ (f 𝒞.∘ 𝒜.unitor.⇒.η X) 𝒞.∘
        S.σ V.unit X
        ≈⟨ S.monad.F.homomorphism ⟩∘⟨refl ⟩
      (S.monad.F.F₁ f 𝒞.∘
        S.monad.F.F₁ (𝒜.unitor.⇒.η X)) 𝒞.∘
        S.σ V.unit X
        ≈⟨ 𝒞.assoc ⟩
      S.monad.F.F₁ f 𝒞.∘
        (S.monad.F.F₁ (𝒜.unitor.⇒.η X) 𝒞.∘
          S.σ V.unit X)
        ≈⟨ 𝒞.Equiv.refl ⟩∘⟨ S.unit-coherence ⟩
      S.monad.F.F₁ f 𝒞.∘
        𝒜.unitor.⇒.η (S.monad.F.F₀ X)
        ∎
      where
        open 𝒞.HomReasoning

    lift-parameterFree : (f : X 𝒞.⇒ Y) →
      Reparameterization 𝒜
        (lift₁ (parameterFree f))
        (parameterFree (S.monad.F.F₁ f))
    lift-parameterFree f =
      mkReparameterization M.id
        (𝒞.Equiv.sym (lift-parameterFree-run f) ○
          identityPreserves {𝒜 = 𝒜} {F = lift₁ (parameterFree f)})
      where
        open 𝒞.HomReasoning

    parameterFreeIdentity : (X : 𝒞.Obj) →
      Reparameterization 𝒜
        (parameterFree (𝒞.id {A = X}))
        (idₚ {𝒜 = 𝒜} {A = X})
    parameterFreeIdentity X =
      mkReparameterization M.id
        (𝒞.Equiv.sym 𝒞.identityˡ ○
          identityPreserves
            {𝒜 = 𝒜} {F = parameterFree (𝒞.id {A = X})})
      where
        open 𝒞.HomReasoning

  leftUnitCoherence : (A : 𝒞.Obj) →
    Reparameterization 𝒜
      (multiplicationPara A ∘ₚ lift₁ (unitPara A))
      (idₚ {𝒜 = 𝒜} {A = S.monad.F.F₀ A})
  leftUnitCoherence A =
    parameterFreeIdentity (S.monad.F.F₀ A) ∘ᵥ
      parameterFree-cell S.monad.identityˡ ∘ᵥ
      parameterFree-compose
        (S.monad.μ.η A)
        (S.monad.F.F₁ (S.monad.η.η A)) ∘ᵥ
      (id₂ ∘ₕ lift-parameterFree (S.monad.η.η A))

  rightUnitCoherence : (A : 𝒞.Obj) →
    Reparameterization 𝒜
      (multiplicationPara A ∘ₚ
        unitPara (S.monad.F.F₀ A))
      (idₚ {𝒜 = 𝒜} {A = S.monad.F.F₀ A})
  rightUnitCoherence A =
    parameterFreeIdentity (S.monad.F.F₀ A) ∘ᵥ
      parameterFree-cell S.monad.identityʳ ∘ᵥ
      parameterFree-compose
        (S.monad.μ.η A)
        (S.monad.η.η (S.monad.F.F₀ A))

  associativityCoherence : (A : 𝒞.Obj) →
    Reparameterization 𝒜
      (multiplicationPara A ∘ₚ
        lift₁ (multiplicationPara A))
      (multiplicationPara A ∘ₚ
        multiplicationPara (S.monad.F.F₀ A))
  associativityCoherence A =
    parameterFree-compose⁻¹
      (S.monad.μ.η A)
      (S.monad.μ.η (S.monad.F.F₀ A)) ∘ᵥ
    parameterFree-cell S.monad.assoc ∘ᵥ
    parameterFree-compose
      (S.monad.μ.η A)
      (S.monad.F.F₁ (S.monad.μ.η A)) ∘ᵥ
    (id₂ ∘ₕ lift-parameterFree (S.monad.μ.η A))

  leftUnitCoherence-map : (A : 𝒞.Obj) →
    mapParameters (leftUnitCoherence A) M.≈
      V.unitorˡ.to
  leftUnitCoherence-map A = begin
    (((M.id V.⊗₁ M.id) M.∘ V.unitorˡ.to) M.∘ M.id)
      M.∘ M.id
      ≈⟨ M.identityʳ ⟩
    ((M.id V.⊗₁ M.id) M.∘ V.unitorˡ.to) M.∘ M.id
      ≈⟨ M.identityʳ ⟩
    (M.id V.⊗₁ M.id) M.∘ V.unitorˡ.to
      ≈⟨ V.⊗.identity ⟩∘⟨refl ⟩
    M.id M.∘ V.unitorˡ.to
      ≈⟨ M.identityˡ ⟩
    V.unitorˡ.to
      ∎
    where
      open M.HomReasoning

  rightUnitCoherence-map : (A : 𝒞.Obj) →
    mapParameters (rightUnitCoherence A) M.≈
      V.unitorˡ.to
  rightUnitCoherence-map A = begin
    (V.unitorˡ.to M.∘ M.id) M.∘ M.id
      ≈⟨ M.identityʳ ⟩
    V.unitorˡ.to M.∘ M.id
      ≈⟨ M.identityʳ ⟩
    V.unitorˡ.to
      ∎
    where
      open M.HomReasoning

  associativityCoherence-map : (A : 𝒞.Obj) →
    mapParameters (associativityCoherence A) M.≈ M.id
  associativityCoherence-map A = begin
    ((((M.id V.⊗₁ M.id) M.∘ V.unitorˡ.to) M.∘ M.id)
      M.∘ V.unitorˡ.from)
      ≈⟨ M.identityʳ ⟩∘⟨refl ⟩
    ((M.id V.⊗₁ M.id) M.∘ V.unitorˡ.to) M.∘
      V.unitorˡ.from
      ≈⟨ M.assoc ⟩
    (M.id V.⊗₁ M.id) M.∘
      (V.unitorˡ.to M.∘ V.unitorˡ.from)
      ≈⟨ V.⊗.identity ⟩∘⟨ V.unitorˡ.isoˡ ⟩
    M.id M.∘ M.id
      ≈⟨ M.identity² ⟩
    M.id
      ∎
    where
      open M.HomReasoning

  -- agda-categories currently has no pseudonatural-transformation,
  -- modification, or pseudomonad record. This specialized certificate stores
  -- exactly the induced Para data: the underlying pseudofunctor, weak unit and
  -- multiplication components, invertible pseudonaturality cells, and the
  -- three monad coherence components. The final normal-form fields are the
  -- equalities observed by Para's hom categories.
  record ParaPseudomonad :
    Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞) where
    field
      unitPseudonaturality :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        Reparameterization 𝒜
          (unitPara B ∘ₚ K)
          (lift₁ K ∘ₚ unitPara A)
      unitPseudonaturality⁻¹ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        Reparameterization 𝒜
          (lift₁ K ∘ₚ unitPara A)
          (unitPara B ∘ₚ K)
      unitPseudonaturality-isoˡ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        (unitPseudonaturality⁻¹ K ∘ᵥ
          unitPseudonaturality K) ≈ id₂
      unitPseudonaturality-isoʳ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        (unitPseudonaturality K ∘ᵥ
          unitPseudonaturality⁻¹ K) ≈ id₂
      multiplicationPseudonaturality :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        Reparameterization 𝒜
          (multiplicationPara B ∘ₚ lift₂ K)
          (lift₁ K ∘ₚ multiplicationPara A)
      multiplicationPseudonaturality⁻¹ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        Reparameterization 𝒜
          (lift₁ K ∘ₚ multiplicationPara A)
          (multiplicationPara B ∘ₚ lift₂ K)
      multiplicationPseudonaturality-isoˡ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        (multiplicationPseudonaturality⁻¹ K ∘ᵥ
          multiplicationPseudonaturality K) ≈ id₂
      multiplicationPseudonaturality-isoʳ :
        ∀ {A B : 𝒞.Obj} (K : Para 𝒜 A B) →
        (multiplicationPseudonaturality K ∘ᵥ
          multiplicationPseudonaturality⁻¹ K) ≈ id₂
      leftUnit : (A : 𝒞.Obj) →
        Reparameterization 𝒜
          (multiplicationPara A ∘ₚ lift₁ (unitPara A))
          (idₚ {𝒜 = 𝒜} {A = S.monad.F.F₀ A})
      rightUnit : (A : 𝒞.Obj) →
        Reparameterization 𝒜
          (multiplicationPara A ∘ₚ
            unitPara (S.monad.F.F₀ A))
          (idₚ {𝒜 = 𝒜} {A = S.monad.F.F₀ A})
      associativity : (A : 𝒞.Obj) →
        Reparameterization 𝒜
          (multiplicationPara A ∘ₚ
            lift₁ (multiplicationPara A))
          (multiplicationPara A ∘ₚ
            multiplicationPara (S.monad.F.F₀ A))
      leftUnit-normal : (A : 𝒞.Obj) →
        mapParameters (leftUnit A) M.≈ V.unitorˡ.to
      rightUnit-normal : (A : 𝒞.Obj) →
        mapParameters (rightUnit A) M.≈ V.unitorˡ.to
      pseudonaturality-on-cells :
        ∀ {A B : 𝒞.Obj} {K L : Para 𝒜 A B}
          (α : Reparameterization 𝒜 K L) →
        ((M.id V.⊗₁ mapParameters α) M.∘
          unitSwap (Parameters L))
          M.≈
        (unitSwap (Parameters K) M.∘
          (mapParameters α V.⊗₁ M.id))
      associativity-normal : (A : 𝒞.Obj) →
        mapParameters (associativity A) M.≈ M.id

  liftPseudomonad : ParaPseudomonad
  liftPseudomonad = record
    { unitPseudonaturality = unitNaturality
    ; unitPseudonaturality⁻¹ = unitNaturality⁻¹
    ; unitPseudonaturality-isoˡ = unitNaturality-isoˡ
    ; unitPseudonaturality-isoʳ = unitNaturality-isoʳ
    ; multiplicationPseudonaturality = multiplicationNaturality
    ; multiplicationPseudonaturality⁻¹ = multiplicationNaturality⁻¹
    ; multiplicationPseudonaturality-isoˡ =
        multiplicationNaturality-isoˡ
    ; multiplicationPseudonaturality-isoʳ =
        multiplicationNaturality-isoʳ
    ; leftUnit = leftUnitCoherence
    ; rightUnit = rightUnitCoherence
    ; associativity = associativityCoherence
    ; leftUnit-normal = leftUnitCoherence-map
    ; rightUnit-normal = rightUnitCoherence-map
    ; pseudonaturality-on-cells = λ α →
        unitSwap-natural (mapParameters α)
    ; associativity-normal = associativityCoherence-map
    }

  open ParaPseudomonad public
