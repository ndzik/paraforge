{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning.Architecture.Wiring where

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import ParaForge.Architecture.Signature
open import ParaForge.Architecture.Wiring
open import ParaForge.Learning.Interface
open import ParaForge.Learning.Algebra
open import ParaForge.Learning.Lens

-- A dataflow interpretation states how tensor interface codes are represented
-- in both directions. The inverse and monoid-compatibility laws prevent a
-- model from giving structural wiring an incoherent product encoding.
record DataflowLearningModel
  {i p g : Level}
  {Σ : Signature i p g}
  (D : DataflowSignature Σ)
  (v f : Level) : Set (suc (i ⊔ p ⊔ g ⊔ v ⊔ f)) where
  private
    module S = Signature Σ
    module D = DataflowSignature D

  field
    interpretInterface : S.InterfaceCode → FeedbackInterface v f

    unitValue : Value (interpretInterface D.unitInterface)
    unitValue-unique :
      ∀ value → value ≡ unitValue

    tensorValue : ∀ {A B} →
      Value (interpretInterface A) × Value (interpretInterface B) →
      Value (interpretInterface (D.tensorInterface A B))

    untensorValue : ∀ {A B} →
      Value (interpretInterface (D.tensorInterface A B)) →
      Value (interpretInterface A) × Value (interpretInterface B)

    tensorFeedback : ∀ {A B} →
      Feedback (interpretInterface A) × Feedback (interpretInterface B) →
      Feedback (interpretInterface (D.tensorInterface A B))

    untensorFeedback : ∀ {A B} →
      Feedback (interpretInterface (D.tensorInterface A B)) →
      Feedback (interpretInterface A) × Feedback (interpretInterface B)

    untensor-tensor-value : ∀ {A B} left right →
      untensorValue {A} {B} (tensorValue (left , right)) ≡
      (left , right)

    tensor-untensor-value : ∀ {A B} value →
      tensorValue {A} {B} (untensorValue value) ≡ value

    untensor-tensor-feedback : ∀ {A B} left right →
      untensorFeedback {A} {B} (tensorFeedback (left , right)) ≡
      (left , right)

    tensor-untensor-feedback : ∀ {A B} feedback →
      tensorFeedback {A} {B} (untensorFeedback feedback) ≡ feedback

    feedbackAlgebra : ∀ A → FeedbackMonoid (interpretInterface A)

    tensor-empty-compatible : ∀ {A B} →
      untensorFeedback
        (emptyFeedback
          (feedbackAlgebra (D.tensorInterface A B))) ≡
      ( emptyFeedback (feedbackAlgebra A)
      , emptyFeedback (feedbackAlgebra B)
      )

    tensor-combine-compatible : ∀ {A B} first second →
      untensorFeedback
        (_<>ᶠ_ (feedbackAlgebra (D.tensorInterface A B)) first second) ≡
      ( _<>ᶠ_ (feedbackAlgebra A)
          (proj₁ (untensorFeedback first))
          (proj₁ (untensorFeedback second))
      , _<>ᶠ_ (feedbackAlgebra B)
          (proj₂ (untensorFeedback first))
          (proj₂ (untensorFeedback second))
      )

open DataflowLearningModel public

module InterpretDataWiring
  {i p g v f : Level}
  {Σ : Signature i p g}
  {D : DataflowSignature Σ}
  (M : DataflowLearningModel D v f) where

  private
    module S = Signature Σ
    module D = DataflowSignature D
    module M = DataflowLearningModel M

    variable
      A B C : S.InterfaceCode

  -- Identity and composition are supplied by LensCategory. These clauses
  -- interpret exactly the structural generators reified by DataWire.
  interpretDataWire :
    DataWire D A B →
    Lens (M.interpretInterface A) (M.interpretInterface B)
  interpretDataWire copyData = lens
    (λ input → M.tensorValue (input , input))
    (λ where
      (_ , feedback) →
        _<>ᶠ_ (M.feedbackAlgebra _)
          (proj₁ (M.untensorFeedback feedback))
          (proj₂ (M.untensorFeedback feedback)))
  interpretDataWire discardData = lens
    (λ _ → M.unitValue)
    (λ _ → emptyFeedback (M.feedbackAlgebra _))
  interpretDataWire swapData = lens
    (λ input → M.tensorValue
      (proj₂ (M.untensorValue input) ,
       proj₁ (M.untensorValue input)))
    (λ where
      (_ , feedback) → M.tensorFeedback
        (proj₂ (M.untensorFeedback feedback) ,
         proj₁ (M.untensorFeedback feedback)))
  interpretDataWire associateˡ = lens
    (λ input →
      let leftMiddle = proj₁ (M.untensorValue input)
          right = proj₂ (M.untensorValue input)
          left = proj₁ (M.untensorValue leftMiddle)
          middle = proj₂ (M.untensorValue leftMiddle)
      in M.tensorValue (left , M.tensorValue (middle , right)))
    (λ where
      (_ , feedback) →
        let left = proj₁ (M.untensorFeedback feedback)
            middleRight =
              proj₂ (M.untensorFeedback feedback)
            middle =
              proj₁ (M.untensorFeedback middleRight)
            right =
              proj₂ (M.untensorFeedback middleRight)
        in M.tensorFeedback
          (M.tensorFeedback (left , middle) , right))
  interpretDataWire associateʳ = lens
    (λ input →
      let left = proj₁ (M.untensorValue input)
          middleRight = proj₂ (M.untensorValue input)
          middle = proj₁ (M.untensorValue middleRight)
          right = proj₂ (M.untensorValue middleRight)
      in M.tensorValue (M.tensorValue (left , middle) , right))
    (λ where
      (_ , feedback) →
        let leftMiddle =
              proj₁ (M.untensorFeedback feedback)
            right = proj₂ (M.untensorFeedback feedback)
            left = proj₁ (M.untensorFeedback leftMiddle)
            middle = proj₂ (M.untensorFeedback leftMiddle)
        in M.tensorFeedback
          (left , M.tensorFeedback (middle , right)))
