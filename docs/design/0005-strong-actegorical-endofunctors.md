# ADR 0005: Lift strong actegorical endofunctors pseudofunctorially

- **Status:** Accepted
- **Date:** 2026-07-31

## Context

An endofunctor `F : C → C` does not automatically act on a parameterized map
`P ⊙ A ⇒ B`. Moving the unchanged parameter through `F` requires actegorical
strength:

```text
σP,A : P ⊙ F A ⇒ F (P ⊙ A)
```

The source paper presents the induced operation on `Para` under strictness
assumptions. ParaForge instead represents weak monoidal and actegory coherence
explicitly and packages `Para(M ↷ C)` as a bicategory.

## Decision

### Strength

`Strength 𝒜 F` consists of a natural transformation

```text
action ∘ (Id × F) ⇒ F ∘ action
```

and two equations:

- AS1 compares strength at the monoidal unit through the action unitor;
- AS2 compares strength at `P ⊗ Q` with successive strengths through the
  action associator.

Naturality is joint in parameter and computation morphisms. The interface is
independent of `Para`, so later strong-monad structure can reuse it.

### Para lift

A strong endofunctor acts on parameterized maps by:

```text
(P , f) ↦ (P , F f ∘ σP,A)
```

It retains parameter objects and G.1 parameter maps literally. Evaluator
preservation follows from strength naturality. AS1 supplies the identity
comparison and AS2 supplies the composition comparison.

Because `Para` is weakly bicategorical, the result is an
`agda-categories` `Pseudofunctor`, not a strict 2-functor. Its identity and
composition comparison cells have identity parameter maps. Their evaluator
proofs use AS1/AS2; pseudofunctor unit and associativity coherence then reduce
to hom-setoid equations in the parameter category.

Parameter restriction commutes with this lift. Comonoid-induced sharing is the
special case obtained by restricting along the copy map.

### Algebras and coalgebras

For a strong endofunctor `S`, ParaForge defines only the typed structure-map
aliases needed at this stage:

```text
Algebra S A   = Para 𝒜 (F A) A
Coalgebra S A = Para 𝒜 A (F A)
```

No lax cells, algebra morphisms, or pseudomonad laws are included yet. Those
belong to the strong-monad and lax-algebra milestones.

## Sets validation

For cartesian `Sets`, the folding functor is:

```text
F X = 1 + A × X
```

with strength:

```text
σ (p , inl unit)    = inl unit
σ (p , inr (a , x)) = inr (a , (p , x))
```

The constant branch discards the parameter being transported through `F`.
This does not remove the parameter of a Para algebra: its complete structure
map still has shape

```text
P × (1 + A × S) → S
```

and can use `P` in both initialization and recurrent branches. Consequently a
Para algebra for this strong functor is exactly the existing executable
`FoldingCell` at the common `Sets` universe level. The direct algebra fold and
the established concrete list fold agree pointwise.

The product functor `O × -` provides a coalgebraic checkpoint. Its coalgebras
have the parameterized state-machine shape:

```text
P × S → O × S
```

All functor, naturality, AS1, and AS2 equations in these instances hold by
pointwise computation.

## Universes

For `M : Category oₘ ℓₘ eₘ` acting on `C : Category o𝒞 ℓ𝒞 e𝒞`:

```text
Strength 𝒜 F          : Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
StrongEndofunctor 𝒜   : Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
Algebra S A           : Set (oₘ ⊔ ℓ𝒞)
Coalgebra S A         : Set (oₘ ⊔ ℓ𝒞)
```

The parameter equality level `eₘ` is not needed by strength itself. The lifted
pseudofunctor retains the universe levels of the existing Para bicategory.

## Consequences

- Strong endofunctors now describe algebraic and coalgebraic architecture
  cells without introducing recursion syntax prematurely.
- Weak coherence remains explicit; no strictification assumption is hidden.
- `Sets` validates both the functor lift and the existing recurrent-cell
  interpretation executably.
- Strong monad unit/multiplication compatibility and lax algebra cells remain
  the next separate layer.
