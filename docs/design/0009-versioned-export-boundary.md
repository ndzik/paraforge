# Versioned architecture export boundary

## Status

Accepted.

## Context

ParaForge's intrinsically typed source architecture retains local primitive
occurrence contexts and a G.1-oriented binding from external parameters to
those occurrences. External runtimes instead need a closed operation tree in
which every trainable primitive refers to one stable external declaration.
Static Agda indices are erased during transport, so an independent runtime must
recheck all shape and reference obligations.

Finite shared repetition presents an additional provenance problem. The source
builder elaborates `repeatShared` to sequential composition, after which a
compiler cannot distinguish repetition from manually repeated syntax without
performing unreliable normalization and pattern recognition.

## Decision

### The IR is a compilation target

`Operation Π A B` is indexed by one global external tensor parameter context
`Π` and input/output shapes. Bound linear and convolution primitives carry a
typed `Slot` into `Π`. Fixed convolution carries a constant code and no
trainable reference. Sequential, parallel, structural wiring, and endomorphic
`Repeat` remain explicitly typed.

Compilation threads a `Selection Π Γ` through an existing
`CartesianArch TensorDataflow Γ A B`. Sequential and parallel composition split
that selection in later-before-earlier order. Parameter restriction transports
the selection through the existing `ParamWire`. The tensor signature has no
generated reparameterizations, so this interpretation is total.

The target is not a second source architecture language: documents are produced
by `compileNetwork` or another typed compilation entry point, not authored as a
replacement for `Network`.

### Repetition is explicit at compilation

The source core is not extended with a repeat constructor. Instead:

```text
compileSharedRollout count step
```

receives the same count and endomorphic source step used by the builder. Zero
emits identity with the empty `sharedContext`; a positive count emits target
`Repeat` over one compiled step and retains one shared external context. The
expanded `repeatShared` source remains the semantic reference.

This avoids guessing repeated subtrees, preserves a compact document, and keeps
all existing source interpretations unchanged.

### Parameter ids are canonical positions

Version 1 serializes external declarations in ParaForge context order and uses
zero-based numeric ids. Typed de Bruijn slots erase to those ids only after
Agda has established that the selected declaration has the required parameter
code. The runtime independently checks that ids are contiguous and each
primitive's referenced declaration has exactly the expected kind and
dimensions.

The NCA declarations are:

```text
0 = pointwise linear 16 → 4
1 = pointwise linear 12 → 16
```

Its repeated execution references are:

```text
[1,0,1,0,1,0,1,0]
```

### JSON is closed and independently validated

The pure Agda renderer fixes schema name, version, field order, constructor
names, parameter order, and a trailing newline. The transport-level JSON Schema
rejects unknown fields and malformed constructor shapes. A standard-library-
only Python parser additionally reconstructs operation input/output shapes and
validates sequential boundaries, structural wiring, parameter references, and
endomorphic repetition.

The runtime never trusts that a document originated in Agda.

### Fixed NCA perception has one meaning

`nca_perception` is a constant source, not a trainable convolution. For every
input channel, its interleaved outputs are identity, Sobel-x, and Sobel-y.
Identity has centre coefficient one. The Sobel filters use the standard integer
kernels divided by eight, and values outside the grid are zero. Every conforming
numerical backend must materialize exactly this constant.

## Consequences

- Source architecture syntax and existing interpretations remain unchanged.
- Export operations refer directly to global external parameter identity.
- Shared rollout parameters remain shared without duplicating declarations.
- Target-level `Repeat` is explicit but never inferred from syntax.
- The checked-in NCA JSON is deterministic and backend-neutral.
- JSON Schema handles transport shape; the strict parser handles dependent
  semantic obligations erased from Agda.
- No array, JAX transformation, initialization, numerical execution,
  differentiation, loss, optimizer, or training behavior enters this boundary.
