{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Set.Reparameterization where

-- Reparameterizations are behavior-preserving 2-cells between parallel
-- parameterized maps. A cell from F = (P , f) to G = (P′ , f′) carries a
-- target-to-source parameter map r : P′ → P and proves
-- f′ (p′ , a) ≡ f (r p′ , a). Thus G factors through F: it can restrict or
-- re-express F's behaviors, but cannot add behavior outside F's family.
--
-- This captures common modeling decisions as explicit parameter maps. For
-- example, p ↦ (p , p) ties two independent weights, (U , V) ↦ U V embeds a
-- low-rank layer into a general matrix layer, and p ↦ (p , … , p) shares one
-- parameter across an unrolled recurrent network. Vertical composition then
-- combines such restrictions while preserving their behavioral guarantees.

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)
  renaming (sym to ≡-sym; trans to ≡-trans)

open import ParaForge.Para.Set

private
  variable
    o p q r s : Level
    A B : Set o
    F : Para {o = o} {p = p} A B
    G : Para {o = o} {p = q} A B
    H : Para {o = o} {p = r} A B
    I : Para {o = o} {p = s} A B

-- A G.1-oriented cell points from F to G, while its parameter map points
-- backwards from G's parameters to F's parameters. The proof ensures that
-- this change of parameters preserves the represented behavior.
-- Check the referenced paper for `G.1`.
-- This is analogous to natural transformations known in the bicategory for `Cat`
-- but here we will call them "reparameterizations".
record Reparameterization
  {o p q : Level} {A B : Set o}
  (F : Para {o = o} {p = p} A B)
  (G : Para {o = o} {p = q} A B) : Set (o ⊔ p ⊔ q) where
  constructor mkReparameterization
  field
    mapParameters : Parameters G → Parameters F
    preserves-run : ∀ targetParameter a →
      run G (targetParameter , a) ≡
      run F (mapParameters targetParameter , a)

open Reparameterization public

-- Just for completion: Cells can be understood here in Para(Set):
-- A, B                         0-cells: sets
-- F, G : Para A B              1-cells: parameterized maps
-- α : Reparameterization F G   2-cell: transformation between those maps
-- So essentially: "morphisms between parallel 1-cells".
--       F
--   A ──────▶ B
--       α
--       ⇓
--   A ──────▶ B
--       G
-- Cells are observed through their parameter maps. Their preservation proofs
-- remain required construction data but are deliberately not compared.
-- "pointwise equivalent"
infix 4 _≈_

_≈_ :
  ∀ {o p q} {A B : Set o}
    {F : Para {o = o} {p = p} A B} {G : Para {o = o} {p = q} A B} →
  Reparameterization F G → Reparameterization F G → Set (p ⊔ q)
α ≈ β = ∀ targetParameter →
  mapParameters α targetParameter ≡ mapParameters β targetParameter

≈-refl : (α : Reparameterization F G) → α ≈ α
≈-refl α targetParameter = refl

≈-sym : {α β : Reparameterization F G} → α ≈ β → β ≈ α
≈-sym α≈β targetParameter = ≡-sym (α≈β targetParameter)

≈-trans : {α β γ : Reparameterization F G} →
  α ≈ β → β ≈ γ → α ≈ γ
≈-trans α≈β β≈γ targetParameter =
  ≡-trans (α≈β targetParameter) (β≈γ targetParameter)

-- We need a helper for equivalence so we use Setoid, since in agda-categories
-- categories are Setoid enriched (AFAIU).
-- So we should be able to say that reparameterizations are categorically equal, when
-- their parameter amps agree pointwise, regardless of how their preservation proofs
-- were constructed.
reparameterizationSetoid :
  ∀ {o p q} {A B : Set o} →
  (F : Para {o = o} {p = p} A B) →
  (G : Para {o = o} {p = q} A B) →
  Setoid (o ⊔ p ⊔ q) (p ⊔ q)
reparameterizationSetoid F G = record
  { Carrier = Reparameterization F G
  ; _≈_ = _≈_
  ; isEquivalence = record
      { refl = λ {α} targetParameter → refl
      ; sym = λ α≈β targetParameter → ≡-sym (α≈β targetParameter)
      ; trans = λ α≈β β≈γ targetParameter →
          ≡-trans (α≈β targetParameter) (β≈γ targetParameter)
      }
  }

identityParameters :
  ∀ {o p} {A B : Set o} {F : Para {o = o} {p = p} A B} →
  Parameters F → Parameters F
identityParameters = id

identityPreserves :
  ∀ {o p} {A B : Set o} {F : Para {o = o} {p = p} A B} →
  ∀ (parameter : Parameters F) a →
  run F (parameter , a) ≡
  run F (identityParameters {F = F} parameter , a)
identityPreserves parameter a = refl

-- Identity 2-cell.
id₂ :
  ∀ {o p} {A B : Set o} {F : Para {o = o} {p = p} A B} →
  Reparameterization F F
id₂ {F = F} = mkReparameterization
  (identityParameters {F = F})
  (identityPreserves {F = F})

-- For α : F ⇒ G and β : G ⇒ H, vertical composition follows the backwards
-- parameter maps: H → G → F.
verticalMap :
  Reparameterization G H →
  Reparameterization F G →
  Parameters H → Parameters F
verticalMap β α targetParameter =
  mapParameters α (mapParameters β targetParameter)

verticalPreserves :
  (β : Reparameterization G H) →
  (α : Reparameterization F G) →
  ∀ targetParameter a →
  run H (targetParameter , a) ≡
  run F (verticalMap β α targetParameter , a)
verticalPreserves β α targetParameter a =
  ≡-trans
    (preserves-run β targetParameter a)
    (preserves-run α (mapParameters β targetParameter) a)

infixr 7 _∘ᵥ_

_∘ᵥ_ :
  Reparameterization G H →
  Reparameterization F G →
  Reparameterization F H
β ∘ᵥ α = mkReparameterization
  (verticalMap β α)
  (verticalPreserves β α)

-- Vertical composition respects the chosen pointwise equality.
∘ᵥ-resp-≈ :
  {α α′ : Reparameterization F G} →
  {β β′ : Reparameterization G H} →
  β ≈ β′ → α ≈ α′ →
  (β ∘ᵥ α) ≈ (β′ ∘ᵥ α′)
∘ᵥ-resp-≈ {α′ = α′} {β = β} β≈β′ α≈α′ targetParameter =
  ≡-trans
    (α≈α′ (mapParameters β targetParameter))
    (cong (mapParameters α′) (β≈β′ targetParameter))

∘ᵥ-identityˡ : (α : Reparameterization F G) →
  (id₂ {F = G} ∘ᵥ α) ≈ α
∘ᵥ-identityˡ α targetParameter = refl

∘ᵥ-identityʳ : (α : Reparameterization F G) →
  (α ∘ᵥ id₂ {F = F}) ≈ α
∘ᵥ-identityʳ α targetParameter = refl

∘ᵥ-assoc :
  (γ : Reparameterization H I) →
  (β : Reparameterization G H) →
  (α : Reparameterization F G) →
  ((γ ∘ᵥ β) ∘ᵥ α) ≈ (γ ∘ᵥ (β ∘ᵥ α))
∘ᵥ-assoc γ β α targetParameter = refl
