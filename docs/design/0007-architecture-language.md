# ADR 0007: Interpretation-first architecture language

- **Status:** Accepted for the Milestone 7 prototype
- **Date:** 2026-08-01

## Context

Milestones 1–6 established executable and generic `Para`, G.1-oriented
reparameterizations, explicit comonoid sharing, strong monads, and the weak
Para-specialized form of Theorem G.10. Before defining an initial architecture
AST, Milestone 7 must show that a proposed operation set handles both a simple
sequential network and cartesian dataflow such as a Transformer encoder block
under at least two useful interpretations.

The two test architectures impose different requirements:

- a two-layer MLP needs typed primitives, sequential composition, normalized
  parameter accumulation, and executable later-before-earlier parameter order;
- a pre-norm Transformer block additionally needs activation fan-out, parallel
  branches, residual recombination, reusable blocks, and independent or shared
  repetition.

Parameter sharing and activation fan-out must not be conflated. The former is a
G.1 target-to-source restriction in the parameter category; the latter is
cartesian structure in the computation semantics.

## Decision

### Validate with a tagless-final interface first

Phase 27 defines `Model`, whose `Architecture Γ A B` family is supplied by each
interpretation. The MLP and Transformer examples are defined once against its
operations:

```text
identity
interpretPrimitive
sequential
parallel
dataWire
restrict
```

This is not an initial architecture AST. It is an interpretation contract used
to discover whether an eventual `CoreArch` would have enough operations.
Reification is deferred to Phase 28.

The prototype uses a small common signature containing vector and token
interfaces and coarse-grained dense, activation, normalization, attention,
feed-forward, and token-addition primitives. Attention deliberately remains
one architecture node; tensor contraction syntax is outside this gate.

### Normalize parameter contexts as typed lists

`ParamCtx` is a typed list of parameter codes. Sequential and parallel
composition use:

```text
laterParameters ++ earlierParameters
```

which is the syntactic normal form corresponding to the established semantic
order `Q ⊗ P`. Parameter-free primitives therefore do not appear as explicit
`I` entries.

Lists do not make both unit laws definitionally true for an unknown context.
In particular, `Γ ++ []` does not reduce to `Γ`. The Transformer residual
example exposed this immediately. `rightUnitWire : ParamWire Γ (Γ ++ [])`
performs the required explicit normalization. The eventual interpreter must
map it to weak monoidal unitor coherence rather than claim strictness.

### Separate data and parameter wiring

`DataWire A B` contains computation-side structural operations such as
activation copy, discard, swap, and reassociation. It supports the derived
residual pattern:

```text
copy input
run a branch beside identity
add the results
```

`ParamWire Δ Γ` instead denotes a typed target-to-source selection from the
external parameter context `Δ` to the untied occurrence context `Γ`. It is
represented by typed de Bruijn slots. Repeated selection is sharing, an unused
external slot is deletion, and reordering is permutation.

`applyWire` maps every such structural wire to an environment function:

```text
Env F Δ → Env F Γ.
```

For the executable interpretation, `restrict wire architecture` is exactly
precomposition by `applyWire wire`. `restrictionCell` packages this as the
existing concrete G.1 `Reparameterization`, with pointwise reflexive
preservation. No competing sharing semantics is introduced.

The common prototype signature is interpreted in cartesian `Sets`, where each
parameter code is shareable. Phase 28 must make shareability requirements
explicit when generalizing the signature and interpreting structural wires in
non-cartesian parameter categories. It must not infer global copying from bare
`Monoidal` or `Actegory` structure.

### Use body plus binding as the symbolic normal form

The symbolic model realizes the proposed representation:

```text
external parameters
untied primitive occurrences
ParamWire external occurrences
ordered symbolic nodes
depth
```

This is a semantic graph summary, not the future initial AST. Sequential and
parallel interpretation preserve raw primitive occurrences while composing
their external binding. Restriction changes only that binding.

## Interpretation results

### Executable Sets checkpoint

Tensor-shaped interfaces are interpreted by lightweight natural-number values.
Dimensions remain intrinsic in interface codes, while primitive evaluators use
addition to expose ordering and data flow without introducing a numerical
tensor backend.

The checked examples establish:

- the MLP receives parameters in output-layer, then input-layer order and
  evaluates `5 + (4 + 3) = 12`;
- the pre-norm Transformer block executes both residual branches and evaluates
  to `17` for its test environment;
- two independently parameterized blocks consume eight values;
- restriction along `duplicateWire` makes two block occurrences consume the
  same four values and produces the same result, `81`.

### Symbolic structure checkpoint

The same definitions produce typed symbolic summaries. The Transformer block
contains, in order:

```text
copy, norm, attention, add,
copy, norm, feed-forward, add
```

Its measured depth is eight. Two independent blocks have eight external
parameters and eight raw occurrences. Two shared blocks retain eight raw
occurrences but expose four external parameters with classes:

```text
[0, 1, 2, 3, 0, 1, 2, 3].
```

The second interpretation is therefore useful for observing topology and
sharing independently of execution.

## Accepted options

- intrinsically indexed architecture representations `Architecture Γ A B`;
- a free syntax over an extensible typed primitive signature in Phase 28;
- a small core with identity, primitives, sequence, parallel dataflow,
  activation wiring, and parameter restriction;
- an ergonomic graph/module layer that elaborates to the core;
- lexical parameter reuse elaborating to explicit `ParamWire` restriction;
- finite independent and shared repetition as derived combinators;
- coarse-grained attention before any tensor-operation language;
- definitional constructor computation, explicit architecture rewrites, and
  semantic hom-setoid coherence as distinct equality layers.

## Rejected options

- syntax represented directly by existing semantic `Para` values, because it
  cannot be reinterpreted;
- an untyped graph AST, because interface and parameter invariants would become
  dynamic checks;
- a sequential-only core, because residual Transformer branches would have to
  be opaque primitives;
- making parameter copy and activation copy the same constructor;
- quotienting syntax by categorical laws;
- claiming list normalization strictifies the weak monoidal semantics;
- expanding attention into tensor contractions before a separate typed tensor
  signature is justified;
- unrestricted recursion in the architecture core.

## Consequences

The interpretation-first gate passes: both models consume the same definitions
and the MLP/Transformer examples require no additional core operation. Phase 28
may now introduce the initial `CoreArch`, provided it:

- preserves the tested `Model` interface;
- keeps sequential and cartesian capability boundaries visible;
- interprets `ParamWire` through existing G.1 restrictions;
- requires explicit parameter-side comonoid evidence outside cartesian models;
- retains unitor and associator normalization as semantic proof obligations;
- reuses the symbolic body-plus-binding behavior rather than conflating graph
  topology with parameter sharing.

## Phase 28 resolution

The reified implementation follows these constraints. `Signature` now carries
separate primitive codes, arbitrary reparameterization generators, and a
`Shareable` capability family. `ParamWire` has two deliberately different
entry points:

```text
generated : ReparameterizationCode Δ Γ → ParamWire Δ Γ
cartesian : AllShareable Δ → Selection Δ Γ → ParamWire Δ Γ.
```

Thus de Bruijn selection is convenient cartesian elaboration only after every
external slot supplies copy/delete capability. It is not evidence that a bare
monoidal category can copy. Semantic models outside cartesian `Sets` must map
that capability to the existing object-local `ParameterComonoid`.

`CoreArch` contains only identity, primitives, sequence, and G.1 restriction.
`CartesianArch` is a separate capability extension with parallel composition
and `DataWire`. `Network` stores an untied `CartesianArch` body together with
its external `ParamWire` binding.

The initial `ArchitectureCell` language contains identity, canonical
restriction, vertical composition, and horizontal sequential composition.
Its executable interpretation uses the existing concrete G.1 cells. Horizontal
preservation required an explicit split/append environment lemma, mirroring the
weak context-normalization obligation rather than relying on equality of
proof-containing records.

## Phase 29 embedded surface

The first surface language is an Agda-embedded builder, not a textual parser.
`Builder` is a collection of smart constructors over `Network`; it has no
separate evaluator. Ordinary composition combines independent external
contexts. Shared-scope composition copies one capability-checked external
context into the two body bindings before composing them.

For the neural signature, a named parameter is an intrinsically typed
`ParameterRef`, implemented by a typed slot in a declaration context. Reusing
the same Agda value is therefore explicit lexical sharing. The elaborated body
still has one slot per primitive occurrence, while its binding records repeated
selection of the external declaration.

Activation reuse remains separate. `fork` elaborates to computation-side
`copyData` followed by parallel branches, and `residualWith` additionally
recombines them with a parameter-free merger. `residualTokens` specializes this
to token addition. Finite `repeatIndependent` tensors external contexts in the
established later-before-earlier order; `repeatShared` retains one context and
uses the same explicit sharing path as lexical reuse.

This surface deliberately uses ordinary Agda names for parameters and named
submodules rather than introducing a parser, name resolver, or second type
checker. Attention remains coarse-grained until a typed tensor-operation
signature is designed independently.
