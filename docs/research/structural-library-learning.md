# Typed architecture search and structural library learning

## Status

Research approach. This note proposes experiments and interfaces; it does not
claim that ParaForge currently performs architecture search or library
learning.

## Research question

Can a learner improve cross-task generalization by discovering a typed library
of reusable architecture schemas, rather than only reusing parameters or
memorizing complete task solutions?

The three relevant learning problems are distinct:

```text
parameter learning:
  fixed architecture → useful parameter values

architecture search:
  one task → useful typed architecture and parameters

library learning:
  many task solutions → reusable typed schemas
```

Parameter learning is an inner process. Architecture search changes one task's
structure. Library learning changes the vocabulary from which future task
structures are built.

## Invariants

1. The existing architecture language remains the single typed source.
2. Search never bypasses input/output interface checking.
3. Activation wiring remains distinct from parameter wiring.
4. Parameter reuse, structural reuse, and functional reuse remain distinct.
5. Every change in parameter identity has an explicit migration or
   initialization policy.
6. Feedback lenses are not assumed to describe global architecture search.
7. Extracted modules are evaluated by held-out transfer, not recurrence alone.
8. Agda owns typed structure and verification; numerical backends own training,
   losses, runtime measurements, and search execution.

## Three nested timescales

For task `τ`, library `L`, architecture `N`, and parameters `p`, the intended
organization is:

```text
inner:   p*     = train(τ, N, p₀)
middle:  N*     = search(τ, Expr(L))
outer:   L*     = extract({N*τ})
```

These loops should remain separately observable. In particular, a library
experiment must report the cost of per-task search and adaptation rather than
counting a pretrained library as free.

## Typed architecture search

For a task with interface `A → B`, every candidate has the form:

```text
N : Network Π A B
```

A candidate packages:

- its architecture and external parameter context `Π`;
- parameter specifications and current values;
- provenance and edit history;
- task loss;
- architecture description cost;
- numerical runtime or resource cost.

A basic task objective is:

```text
taskLossτ(N, p)
  + λ · architectureCost(N)
  + μ · runtimeCost(N)
```

The typed language constrains the search space but does not prescribe the
controller. Enumeration, beam search, evolutionary search, Bayesian search,
reinforcement learning, or a learned proposal model are all possible external
policies.

### Typed edits

The initial edit language should contain small operations whose interface
obligations are explicit:

```text
replace primitive with another A → B primitive
insert an endomorphism A → A
factor or extend sequential composition
introduce or remove a residual branch
introduce compatible parallel structure
change a finite repeat count
share or unshare parameter occurrences
replace a fragment with a library module
```

A structural edit may change the parameter context. It must therefore provide:

```text
old parameter specification → new parameter specification
old parameter values        → initialized or migrated values
old optimizer state          → migrated or reset state
```

General edits are not architecture cells. Existing cells describe compatible
reparameterizations and behavior-preserving structural maps; search may
intentionally change behavior.

## Module discovery

Given task solutions

```text
Nτ₁, Nτ₂, …, Nτₙ
```

module extraction should proceed from strongest and easiest-to-test identity
criteria toward weaker behavioral criteria.

### Exact typed fragments

First derive an analysis fingerprint that ignores irrelevant presentation while
retaining semantic distinctions:

- flatten sequential composition for analysis;
- normalize bound parameter names and de Bruijn references;
- account for unitors, associators, and selected coherence wiring;
- retain activation topology;
- retain the parameter-sharing graph;
- retain input/output interfaces and primitive shape information.

The core syntax should not be quotiented. Normalization is a separate analysis
or certificate-producing interpretation.

Repeated fingerprints yield exact candidate modules:

```text
M : Network Π A B
```

### Typed anti-unification

Exact repetition misses fragments with the same role but different dimensions,
primitives, or children. The next extraction layer computes a typed schema `S`
and substitutions `σᵢ` such that:

```text
instantiate S σ₁ ≈ fragment₁
instantiate S σ₂ ≈ fragment₂
```

A schema may contain typed holes:

```text
normalize >>> hole₁ >>> residual hole₂

hole₁ : A → A
hole₂ : A → A
```

Initially, instantiation should elaborate to ordinary `Network` syntax. A
separate `ModuleCall` core constructor should be introduced only if expansion
becomes an observed problem.

### Behavioral modules

Only later should extraction identify structurally different fragments as the
same module up to:

- parameter reparameterization;
- interface isomorphism;
- a learned and penalized adapter;
- approximate observational behavior;
- causal interchangeability under intervention.

This level faces permutation, latent-coordinate, and distributed-representation
ambiguities. It should not be bundled into the first structural experiment.

## Library entries

A useful library is not a bag of subgraphs. An entry should contain:

```text
LibraryEntry
  typed interface
  implementation or schema
  typed holes and shape variables
  parameter-instantiation policy
  admissible adapters
  provenance and support across tasks
  description and runtime cost
  validation and transfer evidence
```

Parameter-instantiation policies include:

- fresh parameters per use;
- shared parameters across uses;
- frozen pretrained parameters;
- adapted parameters;
- initialization from a learned prior.

These policies distinguish structural reuse from weight tying and parameter
transfer.

## Library objective

Let `Expr(L)` be the typed architectures expressible with library `L`. A
schematic objective is:

```text
cost(L)
  + Στ min N∈Expr(L) (
      descriptionCostL(N)
      + α · taskLossτ(N)
      + β · adaptationCostτ(N)
    )
```

Compression is necessary but insufficient. A valuable module must:

1. compress multiple task solutions;
2. preserve their behavior when factored or substituted;
3. reduce search or adaptation cost on held-out tasks.

The third criterion distinguishes transferable structure from accidental
training-set regularity.

## Cross-task evaluation

The experimental protocol freezes the library before held-out evaluation:

```text
discovery tasks
  → search or train solutions
  → extract and validate library
  → freeze library

held-out tasks
  → search with frozen library
  → measure adaptation and generalization
```

Report at least:

- examples required to reach a target loss;
- optimization steps;
- total search compute;
- wall-clock runtime where meaningful;
- final held-out performance;
- architecture description length;
- fresh parameter count;
- module selection and substitution frequency;
- robustness under interface or domain changes.

### Baselines

- search from scratch under the same budget;
- parameter warm-start without structural reuse;
- structural reuse with fresh parameters;
- a random library of equal size and cost;
- nearest-training-task reuse;
- an oracle library derived from known hidden task structure.

## First experiments

### Structural recovery benchmark

Generate typed architectures from known hidden schemas, then vary their
presentation through:

- reassociation and unit insertion;
- parameter renaming;
- independent versus shared instantiation;
- coherence wiring;
- different well-typed hole implementations.

The extractor should recover the hidden schemas and reject superficially
similar but type- or sharing-incompatible fragments. This benchmark isolates
normalization and anti-unification from numerical optimization.

### Library-assisted numerical search

Use a small task family with controlled overlap, such as:

- elementwise sequence transformations;
- repeated state updates;
- comparison and selection;
- residual correction;
- decomposition and recombination.

Search or train solutions on discovery tasks using an external numerical
backend. Extract and freeze a library, then solve held-out tasks that require
new compositions of familiar motifs. A held-out task with a novel composition
is stronger evidence than another task sampled from an unchanged template.

## Ownership boundary

Agda should own:

- typed architectures, schemas, holes, and instantiation;
- valid structural edits;
- parameter identities and migration descriptions;
- normalization certificates where practical;
- library interfaces and composition checks.

External tooling should own:

- numerical training and evaluation;
- candidate scheduling and search control;
- population and checkpoint management;
- runtime cost measurement;
- statistical mining and approximate behavioral comparison;
- held-out transfer experiments.

The future declarative export boundary must remain backend-neutral. JAX may be
the first numerical implementation, but library semantics must not depend on
JAX transformations or parameter-tree conventions.

## Known failure modes

The approach is weakened if:

- frequent syntax is mistaken for functional reuse;
- the learned library memorizes entire training tasks;
- adapters contain the task-specific computation supposedly factored out;
- weight-sharing search gives misleading candidate rankings;
- routing collapses onto one module or leaves most modules unused;
- the search grammar encodes the intended answer;
- extraction cannot align independently trained representations;
- composition destroys useful isolated behavior;
- task families are too homogeneous to test transfer;
- library search is compared against scratch search with unequal compute;
- categorical abstraction erases locality, causality, cost, or trainability
  needed by the task.

## Progression

```text
typed architecture search
  → exact repeated typed fragments
  → typed anti-unification and schemas
  → library-conditioned search
  → frozen-library held-out transfer
  → approximate behavioral modules
  → extraction from opaque distributed representations
```

The first scientific claim should be modest: typed structural libraries can be
recovered and can reduce held-out search or adaptation cost in a controlled
task family. Stronger claims about reasoning schemas or general intelligence
require materially broader transfer evidence.
