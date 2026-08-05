"""Strict parser for the backend-neutral ParaForge architecture IR.

This module validates structure, shapes, parameter references, and the closed
version-1 operation vocabulary. It deliberately contains no tensor library,
numerical execution, differentiation, or JAX dependency.

All trainable convolutions use zero padding and unit stride. The
``nca_perception`` constant has one version-1 meaning. For each input
channel c, output channels 3c, 3c+1, and 3c+2 are respectively identity,
Sobel-x, and Sobel-y. Identity has centre coefficient 1. Sobel-x is
[[-1, 0, 1], [-2, 0, 2], [-1, 0, 1]] / 8 and Sobel-y is
[[-1, -2, -1], [0, 0, 0], [1, 2, 1]] / 8. The boundary is zero padded.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Iterable, Mapping


SCHEMA_NAME = "paraforge-architecture"
SCHEMA_VERSION = 1


class ValidationError(ValueError):
    """Raised when a document is not a valid ParaForge version-1 IR."""


@dataclass(frozen=True)
class Shape:
    kind: str
    dimensions: tuple[int, ...] = ()
    children: tuple["Shape", ...] = ()


UNIT = Shape("unit")
SCALAR = Shape("scalar")


def vector(features: int) -> Shape:
    return Shape("vector", (features,))


def grid(height: int, width: int, channels: int) -> Shape:
    return Shape("grid", (height, width, channels))


def product(left: Shape, right: Shape) -> Shape:
    return Shape("product", children=(left, right))


@dataclass(frozen=True)
class ParameterSpec:
    identifier: int
    kind: str
    dimensions: tuple[int, ...]


@dataclass(frozen=True)
class Operation:
    kind: str
    input_shape: Shape
    output_shape: Shape
    children: tuple["Operation", ...] = ()
    parameter: int | None = None
    attributes: tuple[tuple[str, object], ...] = ()


@dataclass(frozen=True)
class Document:
    schema: str
    version: int
    input_shape: Shape
    output_shape: Shape
    parameters: tuple[ParameterSpec, ...]
    operation: Operation


def _fail(path: str, message: str) -> ValidationError:
    return ValidationError(f"{path}: {message}")


def _object(value: Any, path: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise _fail(path, "expected an object")
    return value


def _array(value: Any, path: str) -> list[Any]:
    if not isinstance(value, list):
        raise _fail(path, "expected an array")
    return value


def _exact_keys(value: Mapping[str, Any], expected: Iterable[str], path: str) -> None:
    expected_keys = set(expected)
    actual_keys = set(value)
    missing = sorted(expected_keys - actual_keys)
    extra = sorted(actual_keys - expected_keys)
    if missing:
        raise _fail(path, f"missing fields: {', '.join(missing)}")
    if extra:
        raise _fail(path, f"unknown fields: {', '.join(extra)}")


def _string(value: Any, path: str) -> str:
    if not isinstance(value, str):
        raise _fail(path, "expected a string")
    return value


def _integer(value: Any, path: str, *, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise _fail(path, "expected an integer")
    if value < minimum:
        raise _fail(path, f"expected an integer greater than or equal to {minimum}")
    return value


def _positive(value: Any, path: str) -> int:
    return _integer(value, path, minimum=1)


def _tag(value: Mapping[str, Any], path: str) -> str:
    if "type" not in value:
        raise _fail(path, "missing field: type")
    return _string(value["type"], f"{path}.type")


def parse_shape(value: Any, path: str = "shape") -> Shape:
    raw = _object(value, path)
    kind = _tag(raw, path)

    if kind == "unit":
        _exact_keys(raw, ("type",), path)
        return UNIT
    if kind == "scalar":
        _exact_keys(raw, ("type",), path)
        return SCALAR
    if kind == "vector":
        _exact_keys(raw, ("type", "features"), path)
        return vector(_positive(raw["features"], f"{path}.features"))
    if kind == "grid":
        _exact_keys(raw, ("type", "height", "width", "channels"), path)
        return grid(
            _positive(raw["height"], f"{path}.height"),
            _positive(raw["width"], f"{path}.width"),
            _positive(raw["channels"], f"{path}.channels"),
        )
    if kind == "product":
        _exact_keys(raw, ("type", "left", "right"), path)
        return product(
            parse_shape(raw["left"], f"{path}.left"),
            parse_shape(raw["right"], f"{path}.right"),
        )

    raise _fail(f"{path}.type", f"unknown shape {kind!r}")


def _parse_parameter(value: Any, expected_id: int, path: str) -> ParameterSpec:
    raw = _object(value, path)
    if "kind" not in raw:
        raise _fail(path, "missing field: kind")
    kind = _string(raw["kind"], f"{path}.kind")

    if kind == "linear":
        _exact_keys(raw, ("id", "kind", "input_features", "output_features"), path)
        identifier = _integer(raw["id"], f"{path}.id")
        input_features = _positive(raw["input_features"], f"{path}.input_features")
        output_features = _positive(raw["output_features"], f"{path}.output_features")
        spec = ParameterSpec(identifier, kind, (input_features, output_features))
    elif kind == "convolution":
        _exact_keys(
            raw,
            (
                "id",
                "kind",
                "kernel_height",
                "kernel_width",
                "input_channels",
                "output_channels",
            ),
            path,
        )
        identifier = _integer(raw["id"], f"{path}.id")
        spec = ParameterSpec(
            identifier,
            kind,
            (
                _positive(raw["kernel_height"], f"{path}.kernel_height"),
                _positive(raw["kernel_width"], f"{path}.kernel_width"),
                _positive(raw["input_channels"], f"{path}.input_channels"),
                _positive(raw["output_channels"], f"{path}.output_channels"),
            ),
        )
    else:
        raise _fail(f"{path}.kind", f"unknown parameter kind {kind!r}")

    if spec.identifier != expected_id:
        raise _fail(
            f"{path}.id",
            f"expected canonical external parameter id {expected_id}, got {spec.identifier}",
        )
    return spec


def _parameter(
    parameters: tuple[ParameterSpec, ...], identifier: Any, expected: ParameterSpec, path: str
) -> int:
    index = _integer(identifier, path)
    if index >= len(parameters):
        raise _fail(path, f"unknown external parameter id {index}")
    actual = parameters[index]
    if actual.kind != expected.kind or actual.dimensions != expected.dimensions:
        raise _fail(
            path,
            f"parameter {index} has specification {actual.kind}{actual.dimensions}, "
            f"expected {expected.kind}{expected.dimensions}",
        )
    return index


def _require_product(shape: Shape, path: str) -> tuple[Shape, Shape]:
    if shape.kind != "product" or len(shape.children) != 2:
        raise _fail(path, "expected a product shape")
    return shape.children[0], shape.children[1]


def _parse_structural(raw: Mapping[str, Any], kind: str, path: str) -> Operation:
    _exact_keys(raw, ("type", "input", "output"), path)
    input_shape = parse_shape(raw["input"], f"{path}.input")
    output_shape = parse_shape(raw["output"], f"{path}.output")

    if kind == "copy":
        expected_output = product(input_shape, input_shape)
    elif kind == "discard":
        expected_output = UNIT
    elif kind == "swap":
        left, right = _require_product(input_shape, f"{path}.input")
        expected_output = product(right, left)
    elif kind == "associate_left":
        left_pair, third = _require_product(input_shape, f"{path}.input")
        first, second = _require_product(left_pair, f"{path}.input.left")
        expected_output = product(first, product(second, third))
    elif kind == "associate_right":
        first, right_pair = _require_product(input_shape, f"{path}.input")
        second, third = _require_product(right_pair, f"{path}.input.right")
        expected_output = product(product(first, second), third)
    else:
        raise AssertionError(f"unhandled structural operation {kind}")

    if output_shape != expected_output:
        raise _fail(
            f"{path}.output",
            f"{kind} output does not match its structural input",
        )
    return Operation(kind, input_shape, output_shape)


def parse_operation(
    value: Any,
    parameters: tuple[ParameterSpec, ...],
    path: str = "operation",
) -> Operation:
    raw = _object(value, path)
    kind = _tag(raw, path)

    if kind == "identity":
        _exact_keys(raw, ("type", "shape"), path)
        shape = parse_shape(raw["shape"], f"{path}.shape")
        return Operation(kind, shape, shape)

    if kind == "sequential":
        _exact_keys(raw, ("type", "first", "later"), path)
        first = parse_operation(raw["first"], parameters, f"{path}.first")
        later = parse_operation(raw["later"], parameters, f"{path}.later")
        if first.output_shape != later.input_shape:
            raise _fail(path, "sequential intermediate shapes do not match")
        return Operation(
            kind,
            first.input_shape,
            later.output_shape,
            children=(first, later),
        )

    if kind == "parallel":
        _exact_keys(raw, ("type", "left", "right"), path)
        left = parse_operation(raw["left"], parameters, f"{path}.left")
        right = parse_operation(raw["right"], parameters, f"{path}.right")
        return Operation(
            kind,
            product(left.input_shape, right.input_shape),
            product(left.output_shape, right.output_shape),
            children=(left, right),
        )

    if kind in {"copy", "discard", "swap", "associate_left", "associate_right"}:
        return _parse_structural(raw, kind, path)

    if kind == "linear":
        _exact_keys(
            raw,
            ("type", "height", "width", "input_features", "output_features", "parameter"),
            path,
        )
        height = _positive(raw["height"], f"{path}.height")
        width = _positive(raw["width"], f"{path}.width")
        input_features = _positive(raw["input_features"], f"{path}.input_features")
        output_features = _positive(raw["output_features"], f"{path}.output_features")
        expected = ParameterSpec(-1, "linear", (input_features, output_features))
        parameter = _parameter(parameters, raw["parameter"], expected, f"{path}.parameter")
        return Operation(
            kind,
            grid(height, width, input_features),
            grid(height, width, output_features),
            parameter=parameter,
            attributes=(("height", height), ("width", width)),
        )

    if kind == "convolution":
        _exact_keys(
            raw,
            (
                "type",
                "height",
                "width",
                "kernel_height",
                "kernel_width",
                "input_channels",
                "output_channels",
                "parameter",
            ),
            path,
        )
        height = _positive(raw["height"], f"{path}.height")
        width = _positive(raw["width"], f"{path}.width")
        kernel_height = _positive(raw["kernel_height"], f"{path}.kernel_height")
        kernel_width = _positive(raw["kernel_width"], f"{path}.kernel_width")
        input_channels = _positive(raw["input_channels"], f"{path}.input_channels")
        output_channels = _positive(raw["output_channels"], f"{path}.output_channels")
        expected = ParameterSpec(
            -1,
            "convolution",
            (kernel_height, kernel_width, input_channels, output_channels),
        )
        parameter = _parameter(parameters, raw["parameter"], expected, f"{path}.parameter")
        return Operation(
            kind,
            grid(height, width, input_channels),
            grid(height, width, output_channels),
            parameter=parameter,
            attributes=(
                ("kernel_height", kernel_height),
                ("kernel_width", kernel_width),
                ("boundary", "zero"),
                ("stride", 1),
            ),
        )

    if kind == "fixed_convolution":
        _exact_keys(raw, ("type", "height", "width", "kernel"), path)
        height = _positive(raw["height"], f"{path}.height")
        width = _positive(raw["width"], f"{path}.width")
        kernel = _object(raw["kernel"], f"{path}.kernel")
        _exact_keys(kernel, ("type", "channels", "boundary"), f"{path}.kernel")
        kernel_type = _string(kernel["type"], f"{path}.kernel.type")
        if kernel_type != "nca_perception":
            raise _fail(f"{path}.kernel.type", f"unknown fixed kernel {kernel_type!r}")
        channels = _positive(kernel["channels"], f"{path}.kernel.channels")
        boundary = _string(kernel["boundary"], f"{path}.kernel.boundary")
        if boundary != "zero":
            raise _fail(f"{path}.kernel.boundary", "nca_perception requires zero padding")
        return Operation(
            kind,
            grid(height, width, channels),
            grid(height, width, 3 * channels),
            attributes=(
                ("kernel", "nca_perception"),
                ("channels", channels),
                ("boundary", boundary),
            ),
        )

    if kind == "activation":
        _exact_keys(raw, ("type", "height", "width", "channels", "activation"), path)
        height = _positive(raw["height"], f"{path}.height")
        width = _positive(raw["width"], f"{path}.width")
        channels = _positive(raw["channels"], f"{path}.channels")
        activation = _string(raw["activation"], f"{path}.activation")
        if activation != "relu":
            raise _fail(f"{path}.activation", f"unknown activation {activation!r}")
        shape = grid(height, width, channels)
        return Operation(kind, shape, shape, attributes=(("activation", activation),))

    if kind == "add":
        _exact_keys(raw, ("type", "height", "width", "channels"), path)
        height = _positive(raw["height"], f"{path}.height")
        width = _positive(raw["width"], f"{path}.width")
        channels = _positive(raw["channels"], f"{path}.channels")
        shape = grid(height, width, channels)
        return Operation(kind, product(shape, shape), shape)

    if kind == "repeat":
        _exact_keys(raw, ("type", "count", "body"), path)
        count = _integer(raw["count"], f"{path}.count")
        body = parse_operation(raw["body"], parameters, f"{path}.body")
        if body.input_shape != body.output_shape:
            raise _fail(f"{path}.body", "repeat body must be an endomorphism")
        return Operation(
            kind,
            body.input_shape,
            body.output_shape,
            children=(body,),
            attributes=(("count", count),),
        )

    raise _fail(f"{path}.type", f"unknown operation {kind!r}")


def parse_document(value: Any) -> Document:
    raw = _object(value, "document")
    _exact_keys(
        raw,
        ("schema", "version", "input", "output", "parameters", "operation"),
        "document",
    )

    schema = _string(raw["schema"], "document.schema")
    if schema != SCHEMA_NAME:
        raise _fail("document.schema", f"unsupported schema {schema!r}")

    version = _integer(raw["version"], "document.version")
    if version != SCHEMA_VERSION:
        raise _fail("document.version", f"unsupported schema version {version}")

    input_shape = parse_shape(raw["input"], "document.input")
    output_shape = parse_shape(raw["output"], "document.output")
    parameter_values = _array(raw["parameters"], "document.parameters")
    parameters = tuple(
        _parse_parameter(parameter, index, f"document.parameters[{index}]")
        for index, parameter in enumerate(parameter_values)
    )
    operation = parse_operation(raw["operation"], parameters, "document.operation")

    if operation.input_shape != input_shape:
        raise _fail("document.input", "does not match the operation input shape")
    if operation.output_shape != output_shape:
        raise _fail("document.output", "does not match the operation output shape")

    return Document(schema, version, input_shape, output_shape, parameters, operation)


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValidationError(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def loads_document(text: str) -> Document:
    try:
        value = json.loads(text, object_pairs_hook=_reject_duplicate_keys)
    except json.JSONDecodeError as error:
        raise ValidationError(f"invalid JSON: {error.msg}") from error
    return parse_document(value)


def load_document(path: str | Path) -> Document:
    return loads_document(Path(path).read_text(encoding="utf-8"))
