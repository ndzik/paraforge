# Deterministic JAX interpretation

## Status

Accepted.

## Context

The version-1 export boundary contains closed tensor and structural operations,
canonical external parameter declarations, and no numerical values. Agda proves
source-level shape compatibility and parameter typing; the strict Python parser
reconstructs these obligations after erasure. A numerical backend must now give
each validated constructor one concrete forward meaning without moving arrays,
dtypes, devices, random state, or initialization into the architecture IR.

## Decision

### Runtime values follow structural shapes

The JAX interpreter uses unbatched values:

```text
unit          ↦ ()
scalar        ↦ array with shape ()
vector F      ↦ array with shape (F,)
grid H W C    ↦ array with shape (H, W, C)
product A B   ↦ pair (Value A, Value B)
```

Every array leaf must have a floating JAX dtype. Every recursive operation
checks its input and output against the shape reconstructed by the parser.
Products are not concatenated numerical axes.
Copying returns two immutable references to one value; discard returns unit;
swap and reassociation only rearrange pairs.

### Parameter identity is positional

Trainable values form one immutable tuple in canonical external parameter-ID
order. A linear parameter contains an IO weight matrix and output bias. A
convolution parameter contains an HWIO kernel and output-channel bias. Runtime
application verifies the tuple length, constructor, shape, floating dtype, and
matching weight/bias dtypes before execution.

Operations look up this tuple directly by their validated numeric reference.
Repeated or otherwise shared references therefore receive exactly one
parameter value. Fixed kernels never enter the tuple.

### Initialization is an explicit policy

Initialization has the pure boundary:

```text
initialize : Document × JaxKey → ParameterTuple
```

The caller supplies the key. Parameter ID `i` receives
`jax.random.fold_in(key, i)`, so its value is stable under the addition of later
declarations. Weights use Glorot-uniform initialization, biases are zero, and
the default dtype is float32. This is a policy of the first JAX runtime rather
than architecture data or an Agda theorem. Supplying explicit parameter values
remains separate from initialization.

### Numerical constructors have one version-1 meaning

- Linear applies an IO matrix pointwise over the final grid axis and then adds
  its output bias.
- Convolution applies an HWC/HWIO cross-correlation with unit stride and zero
  padding. For kernel extent `k`, `floor((k - 1) / 2)` zeros precede the input
  and the remainder follow it; this fixes even-kernel behavior.
- Fixed NCA perception materializes the interleaved identity, Sobel-x, and
  Sobel-y HWIO bank already fixed by the export contract. It uses the input
  value's dtype and no trainable declaration.
- Activation version 1 is `jax.nn.relu`.
- Add performs elementwise addition of the two equal-shaped grid values.

Sequential and parallel operations recursively follow the validated operation
tree. `Repeat n` performs `n` applications of one endomorphic body while
closing over the same immutable parameter tuple. Its current implementation
uses a static Python loop, which JAX traces successfully for the small exported
count and makes no hidden allocation or random-key use.

### Forward execution remains pure

The public execution boundary is:

```text
apply : Document × ParameterTuple × InputValue → OutputValue
```

It has no global random state, mutation, initialization, loss, gradient,
optimizer, device selection, checkpoint, or training behavior. A separate
`all_finite` predicate supports explicit numerical checks without changing the
architecture semantics.

## Consequences

- The exported NCA executes as a deterministic `16 × 16 × 4` float32 rollout.
- A fixed key deterministically produces two external parameter values with
  shapes `(16, 4)/(4,)` and `(12, 16)/(16,)`.
- Target-level repetition equals four explicit applications of one shared step.
- The elaborated residual step equals its learned delta plus the identity path.
- The interpreter is compatible with `jax.jit` while retaining recursive shape
  checks at tracing boundaries.
- Numerical semantics are runtime-tested rather than claimed as Agda proofs.
- Automatic differentiation and training can reuse this pure forward function,
  but remain outside this decision.
