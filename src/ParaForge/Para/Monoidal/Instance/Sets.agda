{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Monoidal.Instance.Sets where

open import Level using (Level; suc)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Instance.Sets as SetsMonoidal

import ParaForge.Para.Set as Concrete
import ParaForge.Para.Set.Reparameterization as ConcreteCells
import ParaForge.Para.Monoidal as Generic
import ParaForge.Para.Monoidal.Reparameterization as GenericCells
open import ParaForge.Para.Monoidal.Bicategory using (ParaMonoidal)

private
  variable
    ℓ : Level
    A B D : Set ℓ

-- The cartesian monoidal structure on Sets ℓ. Parameters and interfaces must
-- inhabit this same object universe; the concrete model remains available when
-- independent object and parameter levels are required.
Sets-Monoidal : ∀ {o : Level} → Monoidal (Sets o)
Sets-Monoidal = SetsMonoidal.Product.Sets-Monoidal

MonoidalParaSet :
  (ℓ : Level) → Bicategory (suc ℓ) ℓ ℓ (suc ℓ)
MonoidalParaSet ℓ =
  ParaMonoidal (Sets-Monoidal {o = ℓ})

-- At a common level, generic and concrete 1-cells have the same computational
-- components. We translate structurally instead of equating proof-containing
-- records.
toConcrete :
  Generic.Para (Sets-Monoidal {o = ℓ}) A B →
  Concrete.Para {o = ℓ} {p = ℓ} A B
toConcrete F = Concrete.mkPara
  (Generic.Parameters F)
  (Generic.run F)

fromConcrete :
  Concrete.Para {o = ℓ} {p = ℓ} A B →
  Generic.Para (Sets-Monoidal {o = ℓ}) A B
fromConcrete F = Generic.mkPara
  (Concrete.Parameters F)
  (Concrete.run F)

toConcrete-run :
  (F : Generic.Para (Sets-Monoidal {o = ℓ}) A B) →
  ∀ parameterInput →
  Concrete.run (toConcrete F) parameterInput ≡
    Generic.run F parameterInput
toConcrete-run F parameterInput = refl

fromConcrete-run :
  (F : Concrete.Para {o = ℓ} {p = ℓ} A B) →
  ∀ parameterInput →
  Generic.run (fromConcrete F) parameterInput ≡
    Concrete.run F parameterInput
fromConcrete-run F parameterInput = refl

-- G.1 cells translate in both directions. Generic preservation is pointwise
-- equality in Sets, exactly matching the concrete preservation discipline.
toConcreteCell :
  ∀ {F G : Generic.Para (Sets-Monoidal {o = ℓ}) A B} →
  GenericCells.Reparameterization (Sets-Monoidal {o = ℓ}) F G →
  ConcreteCells.Reparameterization (toConcrete F) (toConcrete G)
toConcreteCell α = ConcreteCells.mkReparameterization
  (GenericCells.mapParameters α)
  λ parameter input → GenericCells.preserves-run α (parameter , input)

fromConcreteCell :
  ∀ {F G : Concrete.Para {o = ℓ} {p = ℓ} A B} →
  ConcreteCells.Reparameterization F G →
  GenericCells.Reparameterization
    (Sets-Monoidal {o = ℓ})
    (fromConcrete F)
    (fromConcrete G)
fromConcreteCell α = GenericCells.mkReparameterization
  (ConcreteCells.mapParameters α)
  λ where
    (parameter , input) → ConcreteCells.preserves-run α parameter input

-- Round trips agree under the observable equality of cells; preservation
-- proof fields are intentionally not compared.
to-from-cell-map :
  ∀ {F G : Concrete.Para {o = ℓ} {p = ℓ} A B}
    (α : ConcreteCells.Reparameterization F G) →
  ConcreteCells._≈_
    (toConcreteCell (fromConcreteCell α))
    α
to-from-cell-map α parameter = refl

from-to-cell-map :
  ∀ {F G : Generic.Para (Sets-Monoidal {o = ℓ}) A B}
    (α : GenericCells.Reparameterization (Sets-Monoidal {o = ℓ}) F G) →
  GenericCells._≈_
    (fromConcreteCell (toConcreteCell α))
    α
from-to-cell-map α parameter = refl

-- Identity and sequential composition have the same evaluator behavior. In
-- particular, composition receives parameters as (outer , inner), i.e. Q × P.
identity-agrees :
  ∀ {A : Set ℓ} parameterInput →
  Concrete.run
      (toConcrete (Generic.idₚ {M = Sets-Monoidal {o = ℓ}} {A = A}))
      parameterInput
    ≡ Concrete.run (Concrete.idₚ {o = ℓ} {p = ℓ} {A = A})
      parameterInput
identity-agrees parameterInput = refl

composition-agrees :
  (G : Generic.Para (Sets-Monoidal {o = ℓ}) B D) →
  (F : Generic.Para (Sets-Monoidal {o = ℓ}) A B) →
  ∀ outerParameter innerParameter input →
  Concrete.run
      (toConcrete (Generic._∘ₚ_ G F))
      ((outerParameter , innerParameter) , input)
    ≡ Concrete.run
      (Concrete._∘ₚ_ (toConcrete G) (toConcrete F))
      ((outerParameter , innerParameter) , input)
composition-agrees G F outerParameter innerParameter input = refl
