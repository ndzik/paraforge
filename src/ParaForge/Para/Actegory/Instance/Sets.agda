{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Actegory.Instance.Sets where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Instance.Sets as SetsMonoidal
import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric

open import ParaForge.Actegory.Core using (Actegory; tensorSelfAction)
import ParaForge.Para.Set as Concrete
import ParaForge.Para.Set.Reparameterization as ConcreteCells
import ParaForge.Para.Monoidal.Instance.Sets as MonoidalSets
import ParaForge.Para.Actegory as General
import ParaForge.Para.Actegory.Reparameterization as GeneralCells
import ParaForge.Para.Actegory.Sharing as Sharing
import ParaForge.Para.Actegory.Instance.Monoidal as SelfAction

private
  variable
    ℓ : Level
    A B : Set ℓ

Sets-Monoidal : ∀ {o : Level} → Monoidal (Sets o)
Sets-Monoidal = SetsMonoidal.Product.Sets-Monoidal

Sets-Actegory : ∀ {o : Level} → Actegory (Sets-Monoidal {o}) (Sets o)
Sets-Actegory = tensorSelfAction Sets-Monoidal

Sets-Symmetric : ∀ {o : Level} → Symmetric (Sets-Monoidal {o})
Sets-Symmetric {o} =
  CartesianSymmetric.symmetric
    (Sets o)
    SetsMonoidal.Product.Sets-is

-- Every object in cartesian Sets has its canonical cocommutative comonoid.
-- The laws are pointwise reflexivity for the product implementation.
Sets-ParameterComonoid :
  (P : Set ℓ) → Sharing.ParameterComonoid (Sets-Monoidal {o = ℓ}) P
Sets-ParameterComonoid P = record
  { μ = λ parameter → parameter , parameter
  ; η = λ _ → tt
  ; assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  }

Sets-ParameterCocommutative :
  (P : Set ℓ) →
  Sharing.CocommutativeParameter
    (Sets-Symmetric {o = ℓ})
    (Sets-ParameterComonoid P)
Sets-ParameterCocommutative P parameter = refl

-- The existing self-action and Sets translations compose without changing
-- parameter objects, evaluators, or target-to-source parameter maps.
toConcrete :
  General.Para (Sets-Actegory {o = ℓ}) A B →
  Concrete.Para {o = ℓ} {p = ℓ} A B
toConcrete F =
  MonoidalSets.toConcrete
    (SelfAction.toMonoidal Sets-Monoidal F)

fromConcrete :
  Concrete.Para {o = ℓ} {p = ℓ} A B →
  General.Para (Sets-Actegory {o = ℓ}) A B
fromConcrete F =
  SelfAction.fromMonoidal Sets-Monoidal
    (MonoidalSets.fromConcrete F)

toConcreteCell :
  ∀ {F G : General.Para (Sets-Actegory {o = ℓ}) A B} →
  GeneralCells.Reparameterization (Sets-Actegory {o = ℓ}) F G →
  ConcreteCells.Reparameterization (toConcrete F) (toConcrete G)
toConcreteCell α =
  MonoidalSets.toConcreteCell
    (SelfAction.toMonoidalCell Sets-Monoidal α)

fromConcreteCell :
  ∀ {F G : Concrete.Para {o = ℓ} {p = ℓ} A B} →
  ConcreteCells.Reparameterization F G →
  GeneralCells.Reparameterization
    (Sets-Actegory {o = ℓ})
    (fromConcrete F)
    (fromConcrete G)
fromConcreteCell α =
  SelfAction.fromMonoidalCell Sets-Monoidal
    (MonoidalSets.fromConcreteCell α)
