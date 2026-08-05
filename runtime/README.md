# ParaForge runtime

This directory is a standalone `uv` project for strict validation and numerical
interpretation of exported ParaForge architecture documents.

Agda owns the typed source architecture and canonical export. This package
independently validates the erased JSON representation before any backend uses
it. The IR parser remains backend-neutral; `jax_interpreter.py` provides the
first deterministic numerical interpretation without adding JAX concepts to
the exported format.

## Forward execution

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

Initialization is deterministic for an explicit key. Application is pure and
reuses canonical external parameter values through composition and repetition.
Losses, differentiation, optimizers, and training are intentionally absent.

## Development

```bash
uv sync
uv run pytest
```

The checked-in `.python-version`, `pyproject.toml`, and `uv.lock` define the
reproducible development environment. `.venv` is local and must not be
committed.
