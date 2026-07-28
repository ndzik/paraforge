# ADR 0002: Generalize through monoidal self-action before actegories

- **Status:** Accepted
- **Date:** 2026-07-28

## Context

The concrete `Para(Set)` milestone established parameterized maps, G.1-oriented reparameterizations, hom-categories, bicategorical coherence, and copy-based weight tying. The next goal is to recover the categorical construction behind these operations without weakening the executable concrete model.

Definition G.1 of the source paper starts with a monoidal category `M` acting on a category `C`. The `agda-categories` dependency already provides monoidal categories, but it does not provide an actegory abstraction. Defining an action interface immediately would therefore require choosing its functors, natural isomorphisms, coherence fields, and universe levels before ParaForge has exercised those choices against an existing generic implementation.

Every monoidal category acts on itself through its tensor product. This self-action retains the non-strict unit and associativity obligations needed by the eventual actegory construction while using an existing, tested interface.

## Decision

ParaForge will generalize in two stages:

1. construct `Para(C)` for a category `C` equipped with `Categories.Category.Monoidal.Core.Monoidal C`, using tensor as the action;
2. extract the minimal actegory interface only after the self-action construction, its bicategory packaging, and its `Sets` specialization are complete.

For the self-action construction, a parameterized morphism from `A` to `B` consists of an object `P` of `C` and a morphism `P ⊗ A ⇒ B`. Sequential composition of `(P , f)` followed by `(Q , g)` uses parameter object `Q ⊗ P`, preserving the order of the concrete `Q × P` implementation.

The generic construction will:

- reuse `Category`, `Monoidal`, categorical morphism equality, and `Categories.Bicategory` from `agda-categories`;
- retain target-to-source G.1 reparameterizations;
- derive weak coherence from the supplied monoidal unitors, associator, naturality, triangle, and pentagon fields;
- keep raw maps and proofs separate from final bicategory packaging;
- preserve the concrete `ParaForge.Para.Set` modules as the executable reference model.

Bare monoidal structure does not provide copying or discarding. Weight tying and shared-parameter folds will therefore remain concrete until an explicit cartesian, counital-copy, or comonoid structure supplies the required maps.

## Universe decision

Let `C : Category o ℓ e`. A generic parameterized morphism stores:

- a parameter object in `Set o`;
- an evaluator morphism in `Set ℓ`.

Consequently the raw 1-cell record lives in `Set (o ⊔ ℓ)`. The equality level `e` is absent from the raw record and enters with the categorical preservation equations and hom-setoid equality of reparameterizations.

A reparameterization stores a morphism at level `ℓ` and a preservation equation at level `e`, so it lives in `Set (ℓ ⊔ e)`. For fixed interfaces, the resulting hom-category has levels:

```text
Category (o ⊔ ℓ) (ℓ ⊔ e) e
```

Universe levels will remain explicit through bicategory packaging. The `Sets` self-action necessarily places parameters, inputs, and outputs in one object universe; it will not silently replace the concrete model's independent object and parameter levels.

## Consequences

- The next implementation can test generic composition and coherence against a mature monoidal API before designing a new action hierarchy.
- The eventual actegory interface will be extracted from concrete proof obligations rather than specified speculatively.
- Some self-action proofs may later be generalized or reused, but the actegory implementation must recover self-action as an instance rather than leave two unrelated constructions.
- Copying and discarding remain visibly stronger assumptions than those required for parameterized composition.

## Rejected alternatives

### Define the actegory interface immediately

Rejected because no dependency interface exists to constrain the design, and premature choices about natural isomorphisms, coherence, and universes would be difficult to validate.

### Stop at monoidal self-action

Rejected because it forces parameter objects and data objects to inhabit the same category. The paper's general construction permits a distinct monoidal parameter category acting on the computation category.

### Replace the concrete implementation during generalization

Rejected because the concrete implementation provides executable behavior, independent object and parameter universes, and existing weight-tying examples that the generic specialization must reproduce.
