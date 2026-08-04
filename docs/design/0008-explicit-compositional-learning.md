# Explicit compositional learning boundary

## Status

Accepted.

## Context

ParaForge already had one intrinsically typed architecture source language with
sequential composition, cartesian dataflow, parameter restriction, sharing,
and an Agda-embedded builder. Learning had to interpret that language without
adding another architecture AST and without turning Agda into a numerical
machine-learning runtime.

The relevant decomposition is:

```text
evaluation        P × A → B
credit assignment P × A × B♭ → P♭ × A♭
parameter update  O × P × P♭ → O × P
```

Neither `A♭` nor `P♭` is assumed to be a gradient. An update policy is separate
from credit assignment and need not implement gradient descent.

## Decision

### Architecture learning is an interpretation

`ArchitectureLearningModel` supplies:

1. typed value and feedback carriers for data interfaces;
2. forward and backward semantics for structural data wiring;
3. typed parameter values, signals, sharing algebras, and declared reverse
   transports for parameter wiring;
4. externally supplied primitive learners.

The generic fold interprets `CoreArch`, `CartesianArch`, and `Network` directly.
Sequential composition evaluates first-to-last and propagates feedback
last-to-first. Its parameter values and signals retain the established
later-before-earlier order. Parallel composition uses the declared tensor
encoding. Restriction sends occurrence signals backward through a
`ParameterLens`.

Architecture cells receive a learning interpretation precisely because every
admitted parameter wire has compatible backward transport. Vertical cell
composition composes those transports; horizontal composition tensors them in
parameter-context order.

### Copying requires backward aggregation

Forward activation copying and parameter sharing do not determine their own
backward behavior. `FeedbackMonoid` supplies an explicitly ordered aggregation.
Commutativity remains optional evidence.

The structural interpretation normalizes parameter wires to occurrence
destinations. Signature-declared opaque reparameterizations produce unknown
destinations rather than an invented reverse map. Repeated known destinations
identify feedback aggregation sites. This makes the shared Transformer stack's
mapping explicit:

```text
occurrences  = [0,1,2,3,0,1,2,3]
aggregations = [0,1,2,3]
```

Activation fan-out remains distinct. Residual aggregation is visible through
reverse traversal of the explicit `copyData` nodes.

### Neural case studies are symbolic

The neural learning witness reuses the existing tiny natural-number forward
semantics solely to compare generic evaluation with the established `Sets`
interpretation. Its backward carrier is a list of symbolic routing events.
Those events record primitive reverse order, residual branch routing, and
parameter destinations; they are not derivatives, VJPs, cotangents, or update
instructions.

The existing MLP, finite independent/shared repetitions, pre-normalized
Transformer block, and independent/shared two-block stacks are interpreted
without syntax changes. No numerical neural architecture is trained in Agda.

## Backend ownership

The categorical boundary is backend-neutral.

Agda owns:

- typed architecture and wiring structure;
- parameter identity, occurrence contexts, restriction, and sharing;
- abstract feedback composition and ordered aggregation;
- symbolic reverse traces and structural verification;
- the tiny exact scalar witness for updater separation.

External numerical backends own:

- tensor and neural kernels;
- numerical losses, derivatives, VJPs, and automatic differentiation;
- optimizers and update implementations;
- batching, randomness, devices, compilation, checkpoints, and training loops.

JAX is the first planned numerical backend, not an assumption of
`ArchitectureLearningModel` or the future declarative export boundary.
Alternative runtimes must be able to consume the same architecture contract.

## Consequences

- Architecture syntax remains the single typed source.
- Primitive reverse behavior is explicit model input and cannot be inferred
  from an arbitrary forward function.
- Shared parameters expose both forward identity and backward aggregation
  destinations.
- Structural examples can falsify ordering and routing mistakes without
  duplicating numerical backend behavior.
- Numerical neural validation begins only after crossing the separate typed
  export boundary.
