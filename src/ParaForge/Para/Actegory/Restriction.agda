{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Restriction where

open import Level using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- Restriction introduces no universe growth: restricted maps remain in
-- Set (oₘ ⊔ ℓ𝒞), canonical cells in Set (ℓₘ ⊔ e𝒞), evaluator laws in e𝒞,
-- and cell-equality laws in eₘ.
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

  -- Restriction is contravariant reindexing of an evaluator along a parameter
  -- morphism. It requires no copy or discard structure on the parameter
  -- category.
  restrictParameters :
    (F : Para 𝒜 A B) →
    ∀ {Q : M.Obj} → Q M.⇒ Parameters F →
    Para 𝒜 A B
  restrictParameters F {Q} r =
    mkPara Q (run F 𝒞.∘ (r 𝒜.⊙₁ 𝒞.id))

  -- Definition G.1 points the cell towards the restricted evaluator while its
  -- parameter map points back to the original parameter object.
  restrictCell :
    (F : Para 𝒜 A B) →
    ∀ {Q : M.Obj} (r : Q M.⇒ Parameters F) →
    Reparameterization 𝒜 F (restrictParameters F r)
  restrictCell F r =
    mkReparameterization r 𝒞.Equiv.refl

  restrict-identity-run :
    (F : Para 𝒜 A B) →
    run (restrictParameters F M.id) 𝒞.≈ run F
  restrict-identity-run F =
    𝒞.Equiv.sym (identityPreserves {𝒜 = 𝒜} {F = F})

  restrict-compose-run :
    (F : Para 𝒜 A B) →
    ∀ {Q R : M.Obj}
      (r : Q M.⇒ Parameters F)
      (s : R M.⇒ Q) →
    run (restrictParameters (restrictParameters F r) s)
      𝒞.≈
    run (restrictParameters F (r M.∘ s))
  restrict-compose-run F r s = begin
    run (restrictParameters (restrictParameters F r) s)
      ≈⟨ 𝒞.assoc ⟩
    run F 𝒞.∘
      ((r 𝒜.⊙₁ 𝒞.id) 𝒞.∘ (s 𝒜.⊙₁ 𝒞.id))
      ≈⟨ 𝒞.Equiv.refl ⟩∘⟨ merge-action {𝒜 = 𝒜} r s ⟩
    run (restrictParameters F (r M.∘ s))
      ∎
    where
      open 𝒞.HomReasoning

  -- The following comparison cells bridge evaluator-equivalent Para records.
  -- This avoids asserting propositional equality of records containing
  -- categorical morphisms and proofs.
  restrict-identity-comparison :
    (F : Para 𝒜 A B) →
    Reparameterization 𝒜 (restrictParameters F M.id) F
  restrict-identity-comparison F =
    mkReparameterization M.id proof
    where
      proof :
        run F 𝒞.≈
        run (restrictParameters F M.id) 𝒞.∘
          (M.id 𝒜.⊙₁ 𝒞.id)
      proof =
        identityPreserves {𝒜 = 𝒜} {F = F}
          ○ identityPreserves
            {𝒜 = 𝒜} {F = restrictParameters F M.id}
        where
          open 𝒞.HomReasoning

  restrict-identity-cell :
    (F : Para 𝒜 A B) →
    (restrict-identity-comparison F ∘ᵥ restrictCell F M.id)
      ≈ id₂
  restrict-identity-cell F = M.identity²

  restrict-compose-comparison :
    (F : Para 𝒜 A B) →
    ∀ {Q R : M.Obj}
      (r : Q M.⇒ Parameters F)
      (s : R M.⇒ Q) →
    Reparameterization 𝒜
      (restrictParameters (restrictParameters F r) s)
      (restrictParameters F (r M.∘ s))
  restrict-compose-comparison F r s =
    mkReparameterization M.id proof
    where
      proof :
        run (restrictParameters F (r M.∘ s))
          𝒞.≈
        run (restrictParameters (restrictParameters F r) s)
          𝒞.∘ (M.id 𝒜.⊙₁ 𝒞.id)
      proof =
        𝒞.Equiv.sym (restrict-compose-run F r s)
          ○ identityPreserves
            {𝒜 = 𝒜}
            {F = restrictParameters (restrictParameters F r) s}
        where
          open 𝒞.HomReasoning

  restrict-compose-cell :
    (F : Para 𝒜 A B) →
    ∀ {Q R : M.Obj}
      (r : Q M.⇒ Parameters F)
      (s : R M.⇒ Q) →
    (restrict-compose-comparison F r s ∘ᵥ
      (restrictCell (restrictParameters F r) s ∘ᵥ
        restrictCell F r))
      ≈ restrictCell F (r M.∘ s)
  restrict-compose-cell F r s = M.identityʳ

  restrict-horizontal-run :
    (G : Para 𝒜 B D) →
    (F : Para 𝒜 A B) →
    ∀ {R Q : M.Obj}
      (s : R M.⇒ Parameters G)
      (r : Q M.⇒ Parameters F) →
    run (restrictParameters G s ∘ₚ restrictParameters F r)
      𝒞.≈
    run (restrictParameters (G ∘ₚ F) (s V.⊗₁ r))
  restrict-horizontal-run G F s r =
    preserves-run (restrictCell G s ∘ₕ restrictCell F r)

  restrict-horizontal-comparison :
    (G : Para 𝒜 B D) →
    (F : Para 𝒜 A B) →
    ∀ {R Q : M.Obj}
      (s : R M.⇒ Parameters G)
      (r : Q M.⇒ Parameters F) →
    Reparameterization 𝒜
      (restrictParameters G s ∘ₚ restrictParameters F r)
      (restrictParameters (G ∘ₚ F) (s V.⊗₁ r))
  restrict-horizontal-comparison G F s r =
    mkReparameterization M.id proof
    where
      proof :
        run (restrictParameters (G ∘ₚ F) (s V.⊗₁ r))
          𝒞.≈
        run (restrictParameters G s ∘ₚ restrictParameters F r)
          𝒞.∘ (M.id 𝒜.⊙₁ 𝒞.id)
      proof =
        𝒞.Equiv.sym (restrict-horizontal-run G F s r)
          ○ identityPreserves
            {𝒜 = 𝒜}
            {F = restrictParameters G s ∘ₚ restrictParameters F r}
        where
          open 𝒞.HomReasoning

  restrict-horizontal-cell :
    (G : Para 𝒜 B D) →
    (F : Para 𝒜 A B) →
    ∀ {R Q : M.Obj}
      (s : R M.⇒ Parameters G)
      (r : Q M.⇒ Parameters F) →
    (restrict-horizontal-comparison G F s r ∘ᵥ
      (restrictCell G s ∘ₕ restrictCell F r))
      ≈ restrictCell (G ∘ₚ F) (s V.⊗₁ r)
  restrict-horizontal-cell G F s r = M.identityʳ
