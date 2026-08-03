{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Lens where

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)

open import Categories.Category.Core using (Category)

open import ParaForge.Learning.Interface

private
  variable
    v f : Level
    A B C D : FeedbackInterface v f

-- A feedback lens evaluates forward and translates feedback in the reverse
-- direction. The original input remains available during propagation.
record Lens
  (A B : FeedbackInterface v f) : Set (v ⊔ f) where
  constructor lens
  field
    forward  : Value A → Value B
    backward : Value A × Feedback B → Feedback A

open Lens public

-- Lenses are compared by all observable forward and backward results. This
-- avoids propositional equality of records containing functions.
record _≈ₗ_ {A B : FeedbackInterface v f}
  (L K : Lens A B) : Set (v ⊔ f) where
  constructor lens≈
  field
    forward-eq  : ∀ input → forward L input ≡ forward K input
    backward-eq : ∀ input feedback →
      backward L (input , feedback) ≡ backward K (input , feedback)

open _≈ₗ_ public

infix 4 _≈ₗ_
infixr 9 _∘ₗ_

idₗ : Lens A A
idₗ = lens
  (λ input → input)
  (λ where (_ , feedback) → feedback)

-- Read `later ∘ₗ first` as first evaluating A → B and later evaluating
-- B → C. Feedback from C passes through later before reaching first.
_∘ₗ_ : Lens B C → Lens A B → Lens A C
later ∘ₗ first = lens
  (λ input → forward later (forward first input))
  (λ where
    (input , feedback) → backward first
      (input , backward later (forward first input , feedback)))

≈ₗ-refl : ∀ {L : Lens A B} → L ≈ₗ L
≈ₗ-refl = lens≈ (λ _ → refl) (λ _ _ → refl)

≈ₗ-sym : ∀ {L K : Lens A B} → L ≈ₗ K → K ≈ₗ L
≈ₗ-sym proof = lens≈
  (λ input → sym (forward-eq proof input))
  (λ input feedback → sym (backward-eq proof input feedback))

≈ₗ-trans : ∀ {L K N : Lens A B} → L ≈ₗ K → K ≈ₗ N → L ≈ₗ N
≈ₗ-trans left right = lens≈
  (λ input → trans
    (forward-eq left input)
    (forward-eq right input))
  (λ input feedback → trans
    (backward-eq left input feedback)
    (backward-eq right input feedback))

lensEquivalence :
  IsEquivalence (_≈ₗ_ {v = v} {f = f} {A = A} {B = B})
lensEquivalence = record
  { refl = ≈ₗ-refl
  ; sym = ≈ₗ-sym
  ; trans = ≈ₗ-trans
  }

∘ₗ-resp-≈ :
  ∀ {first first′ : Lens A B} {later later′ : Lens B C} →
  later ≈ₗ later′ →
  first ≈ₗ first′ →
  (later ∘ₗ first) ≈ₗ (later′ ∘ₗ first′)
∘ₗ-resp-≈ {first = first} {first′ = first′}
  {later = later} {later′ = later′} later≈ first≈ = lens≈
    forward-compatible
    backward-compatible
  where
    forward-compatible : ∀ input →
      forward later (forward first input) ≡
      forward later′ (forward first′ input)
    forward-compatible input = trans
      (cong (forward later) (forward-eq first≈ input))
      (forward-eq later≈ (forward first′ input))

    middle-feedback-compatible : ∀ input feedback →
      backward later (forward first input , feedback) ≡
      backward later′ (forward first′ input , feedback)
    middle-feedback-compatible input feedback = trans
      (cong
        (λ middle → backward later (middle , feedback))
        (forward-eq first≈ input))
      (backward-eq later≈ (forward first′ input) feedback)

    backward-compatible : ∀ input feedback →
      backward first
        (input , backward later (forward first input , feedback)) ≡
      backward first′
        (input , backward later′ (forward first′ input , feedback))
    backward-compatible input feedback = trans
      (cong
        (λ middleFeedback → backward first (input , middleFeedback))
        (middle-feedback-compatible input feedback))
      (backward-eq first≈ input
        (backward later′ (forward first′ input , feedback)))

∘ₗ-assoc :
  (first : Lens A B) →
  (middle : Lens B C) →
  (later : Lens C D) →
  ((later ∘ₗ middle) ∘ₗ first) ≈ₗ
  (later ∘ₗ (middle ∘ₗ first))
∘ₗ-assoc first middle later = ≈ₗ-refl

∘ₗ-identityˡ : (L : Lens A B) → (idₗ ∘ₗ L) ≈ₗ L
∘ₗ-identityˡ L = ≈ₗ-refl

∘ₗ-identityʳ : (L : Lens A B) → (L ∘ₗ idₗ) ≈ₗ L
∘ₗ-identityʳ L = ≈ₗ-refl

-- Feedback interfaces and lenses form a category. Its hom equality is
-- behavioral and pointwise in both directions.
LensCategory :
  ∀ {v f : Level} → Category (suc (v ⊔ f)) (v ⊔ f) (v ⊔ f)
LensCategory {v = v} {f = f} = record
  { Obj = FeedbackInterface v f
  ; _⇒_ = Lens
  ; _≈_ = _≈ₗ_
  ; id = idₗ
  ; _∘_ = _∘ₗ_
  ; assoc = λ {f = first} {g = middle} {h = later} →
      ∘ₗ-assoc first middle later
  ; sym-assoc = λ {f = first} {g = middle} {h = later} →
      ≈ₗ-sym (∘ₗ-assoc first middle later)
  ; identityˡ = λ {f = L} → ∘ₗ-identityˡ L
  ; identityʳ = λ {f = L} → ∘ₗ-identityʳ L
  ; identity² = ∘ₗ-identityˡ idₗ
  ; equiv = lensEquivalence
  ; ∘-resp-≈ = ∘ₗ-resp-≈
  }
