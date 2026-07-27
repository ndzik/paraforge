# ADR 0001: Foundations for the concrete Para kernel

- **Status:** Accepted for the first implementation milestone
- **Date:** 2026-07-27

## Context

ParaForge needs a categorical foundation before it defines parameterized maps. The source paper often reasons in a strict setting, while Agda exposes universe boundaries, proof relevance, non-definitional product coherence, and the distinction between propositional and setoid equality.

The project also depends on `agda-categories`, whose categories are Setoid-enriched and whose modules are developed under `--safe --without-K`.

This record fixes the initial choices for concrete `Para(Set)`. They may be revised only in response to concrete formalization evidence and with a new design record.

## Decision

### Toolchain and dependency boundary

The first milestone targets:

- Agda `2.9.0-7273757`;
- standard library `2.4`;
- `agda-categories` commit `f7e4454b83da085e945e759507f624d88f752f36`.

ParaForge reuses `agda-categories` for categories, hom-setoid reasoning, functors, natural transformations, monoidal and cartesian structure, the `Sets` instance, and bicategory interfaces. It will not define a competing general category hierarchy.

The dependency remains installed outside this repository, so the commit above is a reproducibility requirement rather than a lock enforced by `paraforge.agda-lib`. A reproducible dependency mechanism may be added later without changing the mathematical API.

### Safety and equality theory

All ParaForge modules are checked with:

```agda
{-# OPTIONS --safe --without-K #-}
```

The library descriptor enforces the same options globally.

Consequently:

- project code cannot introduce undeclared postulates or unsafe features;
- global uniqueness of identity proofs is unavailable;
- function extensionality, proof irrelevance, UIP, and quotienting must not be assumed silently;
- ordinary equality elimination, transport, congruence, and `refl` remain available.

### Universe convention

The concrete construction is indexed by two fixed universe levels:

```text
o : object level
p : parameter level

A B : Set o
P   : Set p
f   : P × A -> B
```

We write the resulting construction conceptually as `ParaSet o p`.

Fixing `p` for one construction ensures that all parameterized maps in a hom-category inhabit a common Agda universe. The implementation must remain polymorphic in both `o` and `p`; it must not collapse them merely to silence level constraints.

The record containing `P : Set p` necessarily lives above `p`. This universe growth is expected and should be reflected explicitly in inferred or declared result levels.

### G.1-oriented 2-cells

For parameterized maps:

```text
F = (P  , f ) : A -> B
G = (P' , f') : A -> B
```

a 2-cell `F => G` contains:

```text
r : P' -> P
```

and a pointwise proof:

```text
f' (p' , a) = f (r p' , a)
```

The parameter map points from target parameters to source parameters; the 2-cell points from the original computation to its reparameterized restriction.

### Equality discipline

Evaluation preservation is pointwise propositional equality. This agrees with morphism equality in the `agda-categories` category `Sets`, where functions are related pointwise.

Two parallel 2-cells are equivalent when their underlying reparameterization maps are pointwise equal:

```text
alpha ~= beta  iff  forall p', reparam alpha p' = reparam beta p'
```

Preservation proofs are required to construct 2-cells, but hom-setoid equality does not compare those proof fields. This does not assert proof irrelevance: it deliberately chooses the observable equality of 2-cells.

Categorical laws will be stated using this setoid equality. A law must not be described as definitional equality unless Agda checks it by reduction.

### Weak composition

Sequential composition uses binary products:

```text
(P , f) : A -> B
(Q , g) : B -> C

(Q × P , g after f) : A -> C
```

For three parameterized maps, the two composites have parameter objects:

```text
(R × Q) × P
R × (Q × P)
```

Likewise, composition with an identity introduces `Top × P` or `P × Top`. These types are isomorphic but not definitionally equal in Agda.

Therefore concrete `Para(Set)` is initially formalized as a **bicategory**. Product reassociation and unit elimination produce invertible 2-cells, and their triangle and pentagon coherence laws must be proved. ParaForge will not claim a strict 2-category unless a later strictified representation actually provides strict laws.

### Concrete-first boundary

The first implementation constructs and tests concrete `Para(Set)` before defining a general actegory. After the concrete bicategory is working, the project will decide whether to:

1. generalize first to a monoidal category acting on itself; or
2. define an `M`-actegory interface and general `Para` construction directly.

`agda-categories` currently provides no actegory abstraction, so that interface must be justified by the concrete coherence obligations rather than designed speculatively.

## Consequences

- Core laws can use pointwise and setoid reasoning without function extensionality.
- Equality of proof-containing 2-cell records is neither needed nor exposed as the categorical equality.
- Associators and unitors are real implementation data and proof obligations.
- Packaging the raw operations into `Categories.Bicategory` is expected to be the highest-risk part of the first milestone.
- Structural sharing maps such as copy and discard are separate from the monoidal structure needed merely for composition. Their later abstraction will use cartesian or counital-copy structure.
- The initial API carries explicit object and parameter universe levels.

## Rejected alternatives

### Treat products as strictly associative and unital

Rejected because Agda does not identify the relevant product types definitionally. Assuming strictness would hide the central coherence problem the project intends to study.

### Use propositional equality of complete 2-cell records

Rejected because it would require comparing preservation proofs and would invite function extensionality or proof irrelevance. Pointwise hom-setoid equality captures the intended observable map instead.

### Build a local category-theory hierarchy

Rejected because `agda-categories` already supplies the required foundations and follows the proof-relevant, Setoid-enriched discipline desired by ParaForge.

### Define the general actegory construction first

Rejected for the initial milestone because `agda-categories` has no existing actegory interface and the concrete construction should determine the minimal useful abstraction.
