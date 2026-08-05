# ParaForge

ParaForge is an experimental Agda library for describing parameterized
architectures compositionally. It explores a simple question:

> Can the structure of a model, including parameter identity, sharing, dataflow,
> and learning interfaces, remain explicit and type-checked from categorical
> description to numerical execution?

The project combines categorical foundations, an intrinsically typed
architecture language, symbolic and executable interpretations, and a small
validated JAX bridge. Agda owns structure and static guarantees; Python/JAX
owns numerical arrays and execution.

ParaForge is a research prototype, not a production deep-learning framework.
It is inspired by
[*Categorical Deep Learning is an Algebraic Theory of All
Architectures*](https://arxiv.org/abs/2402.15332) and extends the paper's
parameterized-map perspective toward explicit learning and structural reuse.

## Why ParaForge?

Most model descriptions make computation easy to see but parameter structure
hard to inspect. Sharing, deletion, reparameterization, residual dataflow, and
feedback aggregation often become implicit implementation details.

ParaForge instead treats them as typed structure:

- parameterized computations compose with explicit parameter order;
- parameter sharing is represented by an explicit parameter binding;
- activation wiring is distinct from parameter wiring;
- forward architecture, feedback semantics, and update policy are separate;
- one architecture can be executed, inspected symbolically, or exported;
- numerical runtimes validate the proof-erased boundary independently.

This makes small but important questions mechanically observable: Which
parameter does an occurrence use? Is a repeated block shared or independent?
Where does copied feedback aggregate? Does exported execution preserve the
source architecture's shape and sharing structure?

## Capabilities

### Categorical foundations

ParaForge includes an executable `Para(Set)` reference model and generic
parameterized-map constructions for monoidal self-actions and arbitrary
actegories. The formalization retains weak coherence explicitly and supports:

- parameterized identity and composition;
- G.1-oriented reparameterization;
- weak bicategory structure;
- parameter restriction, copying, deletion, and weight tying;
- strong actegorical endofunctors and monads;
- Para-specialized pseudomonad data;
- lax algebras and induced parameter comonoids.

### Typed architecture language

`ParaForge.Architecture` provides intrinsically typed sequential and cartesian
architecture syntax with:

- typed primitive signatures;
- sequential and parallel composition;
- explicit data fan-out and structural wiring;
- residual builders;
- external parameter bindings;
- lexical parameter references;
- independent and shared finite repetition;
- executable and symbolic interpretations.

Examples include MLPs, pre-normalized Transformer blocks, shared Transformer
stacks, and a neural cellular automaton (NCA).

### Explicit learning semantics

`ParaForge.Learning` models learning separately from forward architecture. It
provides typed feedback interfaces, compositional lenses, parameter signals,
update policies, and explicit backward aggregation for copied or shared values.
These abstractions do not identify feedback with gradients or updates with
gradient descent.

The current neural examples use structural and symbolic feedback descriptions.
Numerical neural derivatives remain the responsibility of an external backend.

### Tensor export and JAX execution

A backend-neutral tensor signature describes grids, linear maps,
convolutions, fixed kernels, activation, addition, and structural products. The
example NCA consists of:

```text
16 × 16 × 4 state
  → fixed identity/Sobel perception
  → pointwise linear 12 → 16
  → ReLU
  → pointwise linear 16 → 4
  → residual state update
  → four shared steps
```

The architecture has two external trainable parameters and eight
parameter-consuming occurrences. It compiles to the canonical
[`examples/nca.json`](examples/nca.json), where target-level repetition retains
one shared step rather than duplicating parameter declarations.

The standalone [`runtime/`](runtime/) package:

- strictly validates the versioned document after proof erasure;
- deterministically initializes parameters from an explicit JAX key;
- interprets every version-1 numerical and structural operation;
- executes the NCA eagerly or with `jax.jit`;
- checks runtime shapes and parameter values, with explicit finite-output tests.

## Quick start

### Check the Agda library

ParaForge depends on `standard-library-2.4` and `agda-categories`, as declared in
[`paraforge.agda-lib`](paraforge.agda-lib).

```bash
agda --build-library
```

All source modules are checked with:

```text
--safe --without-K
```

The formalization uses no postulates or unsafe escape hatches.

### Run the validated JAX runtime

The Python runtime is a locked [`uv`](https://docs.astral.sh/uv/) project:

```bash
cd runtime
uv sync
uv run pytest
```

A minimal forward execution is:

```python
from pathlib import Path

import jax
import jax.numpy as jnp

from paraforge_runtime.ir import load_document
from paraforge_runtime.jax_interpreter import apply, initialize

architecture = load_document(Path("../examples/nca.json"))
parameters = initialize(architecture, jax.random.key(42))
state = jnp.zeros((16, 16, 4), dtype=jnp.float32)
result = apply(architecture, parameters, state)
```

Initialization is reproducible for a fixed key. Forward application is pure and
reuses the same external parameter values wherever the architecture shares
them.

## Conceptual boundary

```text
Agda source architecture
       ├── executable reference interpretation
       ├── symbolic structure and parameter routes
       ├── abstract feedback interpretation
       └── typed export compilation
                    ↓
             canonical JSON
                    ↓
          strict runtime validation
                    ↓
          deterministic JAX execution
```

The division of responsibility is deliberate:

| Agda owns                                    | Numerical backends own         |
| ---                                          | ---                            |
| typed interfaces and composition             | arrays and tensor kernels      |
| parameter identity and sharing               | initialization and devices     |
| structural data and parameter wiring         | automatic differentiation      |
| abstract feedback composition                | losses and optimization        |
| export structure and canonical serialization | training loops and checkpoints |

JAX is the first runtime, not part of the categorical or architecture
interfaces.

## Repository guide

| Path                                                                 | Purpose                                                |
| ---                                                                  | ---                                                    |
| [`src/ParaForge.agda`](src/ParaForge.agda)                           | Concrete executable facade                             |
| [`src/ParaForge/Architecture.agda`](src/ParaForge/Architecture.agda) | Typed architecture facade                              |
| [`src/ParaForge/Learning.agda`](src/ParaForge/Learning.agda)         | Explicit learning facade                               |
| [`src/ParaForge/Examples/`](src/ParaForge/Examples/)                 | Checked examples                                       |
| [`runtime/`](runtime/)                                               | Strict parser and deterministic JAX interpreter        |
| [`schema/`](schema/)                                                 | Closed versioned export schema                         |
| [`docs/design/`](docs/design/)                                       | Architectural decisions and formal design notes        |

Recommended design notes:

- [Foundations](docs/design/0001-foundations.md)
- [Actegory interface](docs/design/0003-actegory-interface.md)
- [Parameter wiring](docs/design/0004-parameter-wiring.md)
- [Architecture language](docs/design/0007-architecture-language.md)
- [Explicit compositional learning](docs/design/0008-explicit-compositional-learning.md)
- [Versioned export boundary](docs/design/0009-versioned-export-boundary.md)
- [Deterministic JAX interpretation](docs/design/0010-deterministic-jax-interpretation.md)

The longer-term typed architecture and library-learning direction is described
in [the structural library learning note](docs/research/structural-library-learning.md).

## Current limitations

- The JAX runtime implements deterministic forward execution only; losses,
  autodiff, optimizers, and training loops are not yet included.
- The tensor export vocabulary is intentionally small and closed.
- Transformer examples are structurally typed but are not exported as complete
  numerical attention kernels.
- Repetition is finite; streams and infinite unrolling are outside the current
  implementation.
- Structural and library learning are research directions, not implemented
  search or extraction systems.
- Runtime semantic correspondence is tested after proof erasure; it is not a
  formal proof of JAX itself.

## Acknowledgements

ParaForge builds on Agda,
[`agda-categories`](https://github.com/agda/agda-categories), and the work of the
categorical deep-learning community. The project began as a way to learn the
material by making its obligations executable; and because category theory is
fun!
