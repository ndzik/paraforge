# ParaForge runtime

This directory is a standalone `uv` project for strict validation and numerical
interpretation of exported ParaForge architecture documents.

Agda owns the typed source architecture and canonical export. This package
independently validates the erased JSON representation before any backend uses
it. JAX-specific execution belongs in a separate interpreter module; the IR
parser remains backend-neutral.

## Development

```bash
uv sync
uv run pytest
```

The checked-in `.python-version`, `pyproject.toml`, and `uv.lock` define the
reproducible development environment. `.venv` is local and must not be
committed.
