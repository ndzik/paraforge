# ADR 0004: Model parameter wiring by restriction and object-level comonoids

- **Status:** Accepted
- **Date:** 2026-07-31

## Context

A bare monoidal category does not provide copying or deletion, and a bare actegory only describes how parameters act on computations. Nevertheless, weight tying requires a map from one shared parameter into several independent parameter slots.

Definition G.1 fixes the relevant orientation. Restricting a source evaluator with parameters `P` to target parameters `Q` requires a parameter morphism pointing backward:

```text
r : Q ⇒ P
```

Copying and deletion must therefore be explicit parameter-side structure rather than fields of `Actegory`.

## Decision

### Canonical restriction

For every parameter morphism `r : Q ⇒ P`, ParaForge defines:

```text
restrictParameters r (P , f)
  = (Q , f ∘ (r ⊙₁ id))
```

and the canonical G.1 cell:

```text
(P , f) ⇒ restrictParameters r (P , f)
```

whose parameter map is `r`. Restriction requires no copy, symmetry, or comonoid assumptions. Identity, composition, and horizontal compatibility are stated with evaluator hom-setoid equality and cell equality, not propositional equality of proof-containing records.

### Object-level comonoids

A copyable parameter object reuses the existing `agda-categories` representation:

```text
ParameterComonoid V P = IsMonoid (monoidal-Op V) P
```

It supplies:

```text
Δ : P ⇒ P ⊗ P
ε : P ⇒ I
```

Two-way weight tying is restriction along `Δ`. Thus an evaluator with independent parameters:

```text
(P ⊗ P) ⊙ A ⇒ B
```

induces one with a shared parameter:

```text
P ⊙ A ⇒ B
```

The G.1 cell points from the untied source to the tied target, while `Δ` points from target parameters back to source parameters.

Object-level structure is sufficient for local sharing. ParaForge does not require every object in the parameter category to be copyable. When a category does provide coherent copying globally, `Categories.Category.Monoidal.CounitalCopy` is adapted to the local representation.

### Coherence and symmetry

Comonoid coassociativity proves that the two explicitly reassociated three-way copying trees agree. The action functor lifts this parameter-map equation to agreement of tied evaluators.

Cocommutativity is separate, optional evidence requiring symmetric monoidal structure:

```text
swap ∘ Δ ≈ Δ
```

Permutation-invariant tying is only exposed under this evidence.

### Counit semantics

The counit constructs projections such as:

```text
P ⊗ Q ⇒ P
P ⊗ Q ⇒ Q
```

which make one target parameter component operationally redundant. The counit does not choose a default element of a parameter object and therefore does not generically remove a required source parameter.

## Sets validation

For cartesian `Sets`, every object has the canonical comonoid:

```text
Δ p = (p , p)
ε p = tt
```

Its laws and cocommutativity hold pointwise. The resulting actegory construction reproduces the existing concrete two-bias weight-tying evaluator and G.1 cell under the established actegory-to-monoidal-to-concrete translations.

Three-way copying also reproduces the shared two-step finite fold. The generic representation normalizes its tensor as `(P × P) × P`, while the existing concrete fold uses `P × (P × P)`; the comparison performs the cartesian associator explicitly rather than claiming definitional equality.

## Universes

For `M : Category oₘ ℓₘ eₘ`:

```text
ParameterComonoid V P : Set (ℓₘ ⊔ eₘ)
```

Copying equations live in the parameter hom equality level `eₘ`. Restriction and sharing do not increase the existing universe levels of actegory-based Para maps or cells.

## Consequences

- Weight sharing is available generically but never implicit in bare `Monoidal` or `Actegory` assumptions.
- Copying laws are inherited from established `agda-categories` structures.
- Cartesian `Sets` remains the executable reference instance.
- Theorem G.10 and deriving comonoids from lax algebra cells remain separate future work.
- Architecture syntax can later treat sharing as an operation whose semantics explicitly requests suitable parameter-side structure.
