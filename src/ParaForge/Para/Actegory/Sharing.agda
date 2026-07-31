{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Sharing where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.CounitalCopy using (CounitalCopy)
import Categories.Category.Monoidal.Properties as MonoidalProperties
open import Categories.Object.Monoid using (IsMonoid)

open import ParaForge.Actegory.Core using (Actegory)
open import ParaForge.Para.Actegory
open import ParaForge.Para.Actegory.Reparameterization
open import ParaForge.Para.Actegory.Restriction

private
  variable
    oₘ ℓₘ eₘ o𝒞 ℓ𝒞 e𝒞 : Level

-- A comonoid in M is a monoid in the monoidal opposite category. Reusing the
-- agda-categories representation keeps copying and counit laws in the
-- parameter category and adds no structure to the actegory itself.
-- ParameterComonoid P lives in Set (ℓₘ ⊔ eₘ); its wiring laws live in eₘ,
-- while restricted Para maps and cells retain their existing universe levels.
module _
  {M : Category oₘ ℓₘ eₘ}
  (V : Monoidal M) where

  private
    module M = Category M

  ParameterComonoid : M.Obj → Set (ℓₘ ⊔ eₘ)
  ParameterComonoid =
    IsMonoid (MonoidalProperties.monoidal-Op V)

-- Parameter-side wiring is independent of the acted-on computation category.
module _
  {M : Category oₘ ℓₘ eₘ}
  {V : Monoidal M} where

  private
    module M = Category M
    module V = Monoidal V

  private
    variable
      P Q : M.Obj

  copyParameter :
    ParameterComonoid V P → P M.⇒ (P V.⊗₀ P)
  copyParameter C = IsMonoid.μ C

  discardParameter :
    ParameterComonoid V P → P M.⇒ V.unit
  discardParameter C = IsMonoid.η C

  -- The two binary trees for sharing one parameter across three slots have a
  -- common codomain after explicit reassociation.
  copyParameter3ˡ :
    ParameterComonoid V P →
    P M.⇒ ((P V.⊗₀ P) V.⊗₀ P)
  copyParameter3ˡ C =
    (copyParameter C V.⊗₁ M.id) M.∘ copyParameter C

  copyParameter3ʳ :
    ParameterComonoid V P →
    P M.⇒ ((P V.⊗₀ P) V.⊗₀ P)
  copyParameter3ʳ C =
    (V.associator.to M.∘
      (M.id V.⊗₁ copyParameter C)) M.∘ copyParameter C

  copyParameter3-coherent :
    (C : ParameterComonoid V P) →
    copyParameter3ˡ C M.≈ copyParameter3ʳ C
  copyParameter3-coherent C = IsMonoid.assoc C

  -- Counits erase a selected tensor component. These projections make a
  -- target parameter component operationally redundant; they do not choose a
  -- default value for an arbitrary parameter object.
  dropLeftParameter :
    ParameterComonoid V P →
    (P V.⊗₀ Q) M.⇒ Q
  dropLeftParameter C =
    V.unitorˡ.from M.∘ (discardParameter C V.⊗₁ M.id)

  dropRightParameter :
    ParameterComonoid V Q →
    (P V.⊗₀ Q) M.⇒ P
  dropRightParameter C =
    V.unitorʳ.from M.∘ (M.id V.⊗₁ discardParameter C)

  dropLeft-copy :
    (C : ParameterComonoid V P) →
    dropLeftParameter C M.∘ copyParameter C M.≈ M.id
  dropLeft-copy C = begin
    dropLeftParameter C M.∘ copyParameter C
      ≈⟨ M.assoc ⟩
    V.unitorˡ.from M.∘
      ((discardParameter C V.⊗₁ M.id) M.∘ copyParameter C)
      ≈˘⟨ M.Equiv.refl ⟩∘⟨ IsMonoid.identityˡ C ⟩
    V.unitorˡ.from M.∘ V.unitorˡ.to
      ≈⟨ V.unitorˡ.isoʳ ⟩
    M.id
      ∎
    where
      open M.HomReasoning

  dropRight-copy :
    (C : ParameterComonoid V P) →
    dropRightParameter C M.∘ copyParameter C M.≈ M.id
  dropRight-copy C = begin
    dropRightParameter C M.∘ copyParameter C
      ≈⟨ M.assoc ⟩
    V.unitorʳ.from M.∘
      ((M.id V.⊗₁ discardParameter C) M.∘ copyParameter C)
      ≈˘⟨ M.Equiv.refl ⟩∘⟨ IsMonoid.identityʳ C ⟩
    V.unitorʳ.from M.∘ V.unitorʳ.to
      ≈⟨ V.unitorʳ.isoʳ ⟩
    M.id
      ∎
    where
      open M.HomReasoning

  -- Cocommutativity is optional object-level evidence. A bare parameter
  -- comonoid does not make sharing invariant under permutations.
  CocommutativeParameter :
    (S : Symmetric V) → ParameterComonoid V P → Set eₘ
  CocommutativeParameter {P = P} S C =
    (S.braiding.⇒.η (P , P) M.∘ copyParameter C)
      M.≈ copyParameter C
    where
      module S = Symmetric S

  swappedCopyParameter :
    (S : Symmetric V) →
    ParameterComonoid V P →
    P M.⇒ (P V.⊗₀ P)
  swappedCopyParameter {P = P} S C =
    S.braiding.⇒.η (P , P) M.∘ copyParameter C
    where
      module S = Symmetric S

  -- A global CounitalCopy provider supplies the local structure and optional
  -- cocommutativity evidence for every parameter object.
  counitalCopyComonoid :
    (S : Symmetric V) →
    CounitalCopy S →
    (P : M.Obj) → ParameterComonoid V P
  counitalCopyComonoid S CC P =
    CounitalCopy.isComonoid CC P

  counitalCopy-cocommutative :
    (S : Symmetric V) →
    (CC : CounitalCopy S) →
    {P : M.Obj} →
    CocommutativeParameter S (counitalCopyComonoid S CC P)
  counitalCopy-cocommutative S CC =
    CounitalCopy.cocommutative CC

-- Architecture-level sharing is canonical restriction along the parameter
-- maps above.
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
      A B : 𝒞.Obj
      P : M.Obj

  untiedParameterPair :
    (P : M.Obj) →
    ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B →
    Para 𝒜 A B
  untiedParameterPair P f = mkPara (P V.⊗₀ P) f

  tieParameterPair :
    (C : ParameterComonoid V P) →
    ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B →
    Para 𝒜 A B
  tieParameterPair {P = P} C f =
    restrictParameters (untiedParameterPair P f) (copyParameter C)

  tieParameterPairCell :
    (C : ParameterComonoid V P) →
    (f : ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    Reparameterization 𝒜
      (untiedParameterPair P f)
      (tieParameterPair C f)
  tieParameterPairCell {P = P} C f =
    restrictCell (untiedParameterPair P f) (copyParameter C)

  untiedParameterTriple :
    (P : M.Obj) →
    ((((P V.⊗₀ P) V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    Para 𝒜 A B
  untiedParameterTriple P f =
    mkPara ((P V.⊗₀ P) V.⊗₀ P) f

  tieParameterTriple :
    (C : ParameterComonoid V P) →
    ((((P V.⊗₀ P) V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    Para 𝒜 A B
  tieParameterTriple {P = P} C f =
    restrictParameters
      (untiedParameterTriple P f)
      (copyParameter3ˡ C)

  tieParameterTripleAlternative :
    (C : ParameterComonoid V P) →
    ((((P V.⊗₀ P) V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    Para 𝒜 A B
  tieParameterTripleAlternative {P = P} C f =
    restrictParameters
      (untiedParameterTriple P f)
      (copyParameter3ʳ C)

  tieParameterTriple-run-coherent :
    (C : ParameterComonoid V P) →
    (f : (((P V.⊗₀ P) V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    run (tieParameterTriple C f)
      𝒞.≈
    run (tieParameterTripleAlternative C f)
  tieParameterTriple-run-coherent C f =
    𝒞.∘-resp-≈ʳ
      (𝒜.action.F-resp-≈
        (copyParameter3-coherent C , 𝒞.Equiv.refl))

  tieParameterPairSwapped :
    (S : Symmetric V) →
    (C : ParameterComonoid V P) →
    ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B →
    Para 𝒜 A B
  tieParameterPairSwapped {P = P} S C f =
    restrictParameters
      (untiedParameterPair P f)
      (swappedCopyParameter S C)

  tieParameterPair-commutative-run :
    (S : Symmetric V) →
    (C : ParameterComonoid V P) →
    CocommutativeParameter S C →
    (f : ((P V.⊗₀ P) 𝒜.⊙₀ A) 𝒞.⇒ B) →
    run (tieParameterPairSwapped S C f)
      𝒞.≈
    run (tieParameterPair C f)
  tieParameterPair-commutative-run S C commutative f =
    𝒞.∘-resp-≈ʳ
      (𝒜.action.F-resp-≈
        (commutative , 𝒞.Equiv.refl))
