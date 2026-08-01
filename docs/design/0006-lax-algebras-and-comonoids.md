# ADR 0006: Derive parameter comonoids from Para lax algebras

- **Status:** Accepted
- **Date:** 2026-08-01

## Context

Theorem G.10 of the source paper states that a lax algebra for the monad induced
on `Para` gives its parameter object a comonoid structure. This is the
categorical source of deletion and weight sharing. ParaForge must express the
result without reversing Definition G.1 cells, strictifying the monoidal
category or actegory, or adding copying to the base `Monoidal` interface.

For a lax algebra structure map

```text
a : (P, a) : T A → A
```

Phase 25 uses the Definition F.2 orientations

```text
ε : id_A ⇒ a ∘ η_A
δ : a ∘ T(a) ⇒ a ∘ μ_A.
```

Because a G.1 cell carries a target-to-source parameter map, these cells expose

```text
map ε : P ⊗ I → I
map δ : P ⊗ I → P ⊗ P.
```

The paper suppresses the unit tensor under strictness assumptions. ParaForge
cannot do so definitionally.

## Decision

### Normalize through the right unitor

The parameter maps induced by the lax cells are:

```text
!P = map ε ∘ ρ⁻¹ : P → I
ΔP = map δ ∘ ρ⁻¹ : P → P ⊗ P.
```

Here `ρ⁻¹` denotes the library's `unitorʳ.to : P → P ⊗ I`. These maps are
implemented as `algebraDiscard` and `algebraCopy`.

The lax unity and associativity equations are observed in the parameter
hom-setoid. They have the exact weak comonoid forms:

```text
λ⁻¹ = (!P ⊗ id) ∘ ΔP
ρ⁻¹ = (id ⊗ !P) ∘ ΔP
(ΔP ⊗ id) ∘ ΔP
  = α⁻¹ ∘ (id ⊗ ΔP) ∘ ΔP.
```

No equality of evaluator-preservation records is required.

### Reuse the existing comonoid type

`laxAlgebraParameterComonoid` packages these maps and laws as:

```text
ParameterComonoid V P = IsMonoid (monoidal-Op V) P.
```

This avoids a duplicate comonoid representation and makes all existing
restriction and sharing operations immediately available.

### Sharing remains restriction

The pair-sharing operation induced by a lax algebra is exactly:

```text
restrictParameters untied algebraCopy.
```

It agrees with `tieParameterPair` instantiated by the extracted comonoid, both
on evaluators and on G.1 cells. Thus sharing is derived structure rather than a
new primitive operation.

### Scope of the weak theorem

`agda-categories` currently has no general pseudonatural transformation,
modification, or pseudomonad API. Phase 24 and Phase 25 therefore store the
induced pseudomonad and lax coherence in Para-specialized forms. The theorem
proved here is correspondingly specialized to the existing weak Para
bicategory: it packages the normalized, machine-checked lax cell maps and laws.
It does not claim a reusable theorem for arbitrary externally supplied
pseudomonads.

## Assumptions and non-assumptions

The construction requires:

- a monoidal parameter category `M`;
- an `M`-actegory `C`;
- a strong actegorical monad;
- a coherent Para lax algebra.

It does **not** require:

- symmetry or braiding;
- cocommutativity;
- cartesian parameters;
- strict monoidal or strict action laws;
- a global `CounitalCopy` provider.

Cocommutativity remains optional evidence. The counit deletes a parameter; it
does not select a default value for arbitrary parameter objects.

## Sets validation

For the exception monad `E ⊎ -`, the validated lax algebra uses a natural
number parameter as the fallback value. Its unit cell discards that fallback
for fresh successes. Its multiplication cell copies the same fallback into
both layers of nested exception interpretation.

The extracted maps compute as:

```text
! n = tt
Δ n = (n, n).
```

They agree pointwise with the canonical cartesian `Sets` comonoid, and induced
pair sharing agrees with the established `tieParameterPair` evaluator and
restriction cell.

## Consequences

- The weak form of Theorem G.10 is machine checked without postulates.
- Weight sharing and deletion are derived from lax algebra coherence.
- Existing generic sharing APIs need no special knowledge of monads or lax
  algebras.
- Symmetry remains separate from copying, so permutation invariance is never
  assumed accidentally.
- The Milestone 7 syntax design can treat sharing as semantically derived while
  deciding whether it should have convenient surface syntax.
