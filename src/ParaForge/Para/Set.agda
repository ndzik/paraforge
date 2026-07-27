{-# OPTIONS --safe --without-K #-}

module ParaForge.Para.Set where

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)

private
  variable
    o p q : Level
    A B C : Set o

-- A parameterized map denotes a family of functions A → B indexed by
-- a parameter type. The parameter universe is explicit and independent
-- from the universe containing the input and output interfaces.
-- Currently the type of "parameterized 1-morphisms". All Para values
-- should utlimately become the 1-morphisms of a bicategory called
-- `Para(Set)`.
-- There is a caveat here regarding the fact that `Para(Set)` cannot be a
-- strict category because products do not associate or eliminate units,
-- but this is a good enough start.
record Para {o p : Level} (A B : Set o) : Set (o ⊔ suc p) where
  constructor mkPara
  field
    Parameters : Set p
    run        : Parameters × A → B

open Para public

-- The identity has no effective parameters. A polymorphic unit keeps its
-- parameter type in the requested parameter universe.
-- Essentially the "identity 1-cell" in concrete `Para(Set)`.
-- Basically discards the unit parameter (it does not care about params) and
-- returns the input.
identityEvaluator : ∀ {o p} {A : Set o} → ⊤ {p} × A → A
identityEvaluator (_ , a) = a

idₚ : ∀ {o p} {A : Set o} → Para {p = p} A A
idₚ = mkPara ⊤ identityEvaluator

-- Sequential behavior composes in the usual order, while parameter types
-- accumulate in the order Q × P from the outer map to the inner map.
-- It is the composition of parameterized maps, read right to left.
infixr 9 _∘ₚ_

-- Read as "g after f", so we run the first map `f` and then the second map `g`.
-- Intuitively it might help to think of layers:
-- f : input layer with parameters P
-- g : output layer with parameters Q
-- g ∘ f is the sequential network contaiing both sets of parameters: `Q × P`.
_∘ₚ_ : Para {p = q} B C → Para {p = p} A B → Para {p = q ⊔ p} A C
g ∘ₚ f = mkPara (Parameters g × Parameters f) λ where
  ((q , p) , a) → run g (q , run f (p , a))
