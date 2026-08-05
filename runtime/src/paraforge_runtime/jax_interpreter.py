"""Deterministic JAX interpretation of validated ParaForge version-1 documents.

Runtime values follow the export shape structure directly:

* unit is ``()``;
* scalar, vector, and grid values are unbatched floating JAX arrays;
* a structural product is a Python pair.

Trainable values form an immutable tuple in canonical external parameter-ID
order. Linear weights use IO layout, convolution kernels use HWIO layout, and
biases use the output feature/channel axis. Initializers fold each canonical ID
into an explicit caller-supplied key, use float32 Glorot-uniform weights by
default, and set biases to zero.

Convolutions are unit-stride HWC/HWIO cross-correlations. Padding is explicit:
for a kernel extent k, floor((k - 1) / 2) zeros precede the input and the
remaining zeros follow it. This preserves spatial dimensions and fixes the
even-kernel convention independently of JAX's padding shorthand.
"""

from __future__ import annotations

from typing import Any, NamedTuple, TypeAlias

import jax
from jax import Array, lax
import jax.numpy as jnp

from paraforge_runtime.ir import Document, Operation, ParameterSpec, Shape


class ExecutionError(ValueError):
    """Raised when runtime values do not satisfy a validated document."""


class LinearParameters(NamedTuple):
    weights: Array
    bias: Array


class ConvolutionParameters(NamedTuple):
    kernel: Array
    bias: Array


ParameterValue: TypeAlias = LinearParameters | ConvolutionParameters
Parameters: TypeAlias = tuple[ParameterValue, ...]
RuntimeValue: TypeAlias = Any


def _error(path: str, message: str) -> ExecutionError:
    return ExecutionError(f"{path}: {message}")


def _array_shape(shape: Shape, path: str) -> tuple[int, ...]:
    if shape.kind == "scalar":
        return ()
    if shape.kind == "vector":
        return (shape.dimensions[0],)
    if shape.kind == "grid":
        return shape.dimensions
    raise _error(path, f"{shape.kind!r} is not an array shape")


def _array(value: RuntimeValue, shape: Shape, path: str) -> Array:
    try:
        result = jnp.asarray(value)
    except (TypeError, ValueError) as error:
        raise _error(path, "expected a numerical array value") from error
    expected = _array_shape(shape, path)
    if result.shape != expected:
        raise _error(path, f"expected array shape {expected}, got {result.shape}")
    if not jnp.issubdtype(result.dtype, jnp.floating):
        raise _error(path, f"expected a floating numerical dtype, got {result.dtype}")
    return result


def _value(value: RuntimeValue, shape: Shape, path: str) -> RuntimeValue:
    if shape.kind == "unit":
        if not isinstance(value, tuple) or len(value) != 0:
            raise _error(path, "expected the unit value ()")
        return ()
    if shape.kind in {"scalar", "vector", "grid"}:
        return _array(value, shape, path)
    if shape.kind == "product":
        if not isinstance(value, tuple) or len(value) != 2:
            raise _error(path, "expected a pair for a product shape")
        left, right = shape.children
        return (
            _value(value[0], left, f"{path}.left"),
            _value(value[1], right, f"{path}.right"),
        )
    raise _error(path, f"unknown runtime shape {shape.kind!r}")


def _floating_dtype(dtype: Any) -> jnp.dtype:
    resolved = jnp.dtype(dtype)
    if not jnp.issubdtype(resolved, jnp.floating):
        raise ExecutionError(f"parameter dtype must be floating, got {resolved}")
    return resolved


def _glorot_uniform(
    key: Array,
    shape: tuple[int, ...],
    fan_in: int,
    fan_out: int,
    dtype: jnp.dtype,
) -> Array:
    limit = jnp.sqrt(jnp.asarray(6.0 / (fan_in + fan_out), dtype=dtype))
    return jax.random.uniform(
        key,
        shape,
        dtype=dtype,
        minval=-limit,
        maxval=limit,
    )


def initialize(
    document: Document,
    key: Array,
    *,
    dtype: Any = jnp.float32,
) -> Parameters:
    """Initialize each external declaration deterministically.

    Parameter ID ``i`` uses ``jax.random.fold_in(key, i)``. Consequently a
    declaration's initialization is independent of later declarations while
    remaining a pure function of the explicit root key and its canonical ID.
    """

    resolved_dtype = _floating_dtype(dtype)
    values: list[ParameterValue] = []
    for specification in document.parameters:
        parameter_key = jax.random.fold_in(key, specification.identifier)
        if specification.kind == "linear":
            input_features, output_features = specification.dimensions
            values.append(
                LinearParameters(
                    _glorot_uniform(
                        parameter_key,
                        (input_features, output_features),
                        input_features,
                        output_features,
                        resolved_dtype,
                    ),
                    jnp.zeros((output_features,), dtype=resolved_dtype),
                )
            )
        elif specification.kind == "convolution":
            kernel_height, kernel_width, input_channels, output_channels = (
                specification.dimensions
            )
            receptive_field = kernel_height * kernel_width
            values.append(
                ConvolutionParameters(
                    _glorot_uniform(
                        parameter_key,
                        (
                            kernel_height,
                            kernel_width,
                            input_channels,
                            output_channels,
                        ),
                        receptive_field * input_channels,
                        receptive_field * output_channels,
                        resolved_dtype,
                    ),
                    jnp.zeros((output_channels,), dtype=resolved_dtype),
                )
            )
        else:
            raise _error(
                f"document.parameters[{specification.identifier}]",
                f"unsupported parameter kind {specification.kind!r}",
            )
    return tuple(values)


def _trainable_array(value: Any, path: str) -> Array:
    try:
        result = jnp.asarray(value)
    except (TypeError, ValueError) as error:
        raise _error(path, "expected a floating numerical array") from error
    if not jnp.issubdtype(result.dtype, jnp.floating):
        raise _error(path, f"expected a floating dtype, got {result.dtype}")
    return result


def _normalize_parameter(
    specification: ParameterSpec,
    value: ParameterValue,
    path: str,
) -> ParameterValue:
    if specification.kind == "linear":
        if not isinstance(value, LinearParameters):
            raise _error(path, "expected LinearParameters")
        input_features, output_features = specification.dimensions
        weights = _trainable_array(value.weights, f"{path}.weights")
        bias = _trainable_array(value.bias, f"{path}.bias")
        if weights.shape != (input_features, output_features):
            raise _error(
                f"{path}.weights",
                f"expected shape {(input_features, output_features)}, got {weights.shape}",
            )
        if bias.shape != (output_features,):
            raise _error(
                f"{path}.bias",
                f"expected shape {(output_features,)}, got {bias.shape}",
            )
        if weights.dtype != bias.dtype:
            raise _error(path, "weight and bias dtypes must match")
        return LinearParameters(weights, bias)

    if specification.kind == "convolution":
        if not isinstance(value, ConvolutionParameters):
            raise _error(path, "expected ConvolutionParameters")
        kernel_height, kernel_width, input_channels, output_channels = (
            specification.dimensions
        )
        expected_kernel = (
            kernel_height,
            kernel_width,
            input_channels,
            output_channels,
        )
        kernel = _trainable_array(value.kernel, f"{path}.kernel")
        bias = _trainable_array(value.bias, f"{path}.bias")
        if kernel.shape != expected_kernel:
            raise _error(
                f"{path}.kernel",
                f"expected shape {expected_kernel}, got {kernel.shape}",
            )
        if bias.shape != (output_channels,):
            raise _error(
                f"{path}.bias",
                f"expected shape {(output_channels,)}, got {bias.shape}",
            )
        if kernel.dtype != bias.dtype:
            raise _error(path, "kernel and bias dtypes must match")
        return ConvolutionParameters(kernel, bias)

    raise _error(path, f"unsupported parameter kind {specification.kind!r}")


def _normalize_parameters(document: Document, values: Parameters) -> Parameters:
    if not isinstance(values, tuple):
        raise _error("parameters", "expected an immutable tuple")
    if len(values) != len(document.parameters):
        raise _error(
            "parameters",
            f"expected {len(document.parameters)} values, got {len(values)}",
        )
    return tuple(
        _normalize_parameter(specification, value, f"parameters[{index}]")
        for index, (specification, value) in enumerate(
            zip(document.parameters, values, strict=True)
        )
    )


def _attributes(operation: Operation) -> dict[str, object]:
    return dict(operation.attributes)


def _padding(kernel_height: int, kernel_width: int) -> tuple[tuple[int, int], ...]:
    before_height = (kernel_height - 1) // 2
    before_width = (kernel_width - 1) // 2
    return (
        (before_height, kernel_height - 1 - before_height),
        (before_width, kernel_width - 1 - before_width),
    )


def _convolution(value: Array, kernel: Array, bias: Array) -> Array:
    kernel_height, kernel_width = kernel.shape[:2]
    result = lax.conv_general_dilated(
        value[jnp.newaxis, ...],
        kernel,
        window_strides=(1, 1),
        padding=_padding(kernel_height, kernel_width),
        dimension_numbers=("NHWC", "HWIO", "NHWC"),
    )
    return result[0] + bias


def nca_perception_kernel(channels: int, *, dtype: Any = jnp.float32) -> Array:
    """Materialize the frozen interleaved identity/Sobel HWIO kernel."""

    if channels <= 0:
        raise ExecutionError("nca perception channels must be positive")
    resolved_dtype = _floating_dtype(dtype)
    identity = jnp.asarray(
        [[0.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 0.0]],
        dtype=resolved_dtype,
    )
    sobel_x = jnp.asarray(
        [[-1.0, 0.0, 1.0], [-2.0, 0.0, 2.0], [-1.0, 0.0, 1.0]],
        dtype=resolved_dtype,
    ) / jnp.asarray(8.0, dtype=resolved_dtype)
    sobel_y = jnp.asarray(
        [[-1.0, -2.0, -1.0], [0.0, 0.0, 0.0], [1.0, 2.0, 1.0]],
        dtype=resolved_dtype,
    ) / jnp.asarray(8.0, dtype=resolved_dtype)

    kernel = jnp.zeros((3, 3, channels, 3 * channels), dtype=resolved_dtype)
    for channel in range(channels):
        kernel = kernel.at[:, :, channel, 3 * channel].set(identity)
        kernel = kernel.at[:, :, channel, 3 * channel + 1].set(sobel_x)
        kernel = kernel.at[:, :, channel, 3 * channel + 2].set(sobel_y)
    return kernel


def _parameter(operation: Operation, parameters: Parameters) -> ParameterValue:
    if operation.parameter is None:
        raise ExecutionError(f"{operation.kind} operation has no parameter reference")
    return parameters[operation.parameter]


def _apply_operation(
    operation: Operation,
    parameters: Parameters,
    value: RuntimeValue,
    path: str,
) -> RuntimeValue:
    input_value = _value(value, operation.input_shape, f"{path}.input")
    kind = operation.kind

    if kind == "identity":
        result = input_value
    elif kind == "sequential":
        first, later = operation.children
        intermediate = _apply_operation(first, parameters, input_value, f"{path}.first")
        result = _apply_operation(later, parameters, intermediate, f"{path}.later")
    elif kind == "parallel":
        left, right = operation.children
        result = (
            _apply_operation(left, parameters, input_value[0], f"{path}.left"),
            _apply_operation(right, parameters, input_value[1], f"{path}.right"),
        )
    elif kind == "copy":
        result = (input_value, input_value)
    elif kind == "discard":
        result = ()
    elif kind == "swap":
        result = (input_value[1], input_value[0])
    elif kind == "associate_left":
        (first, second), third = input_value
        result = (first, (second, third))
    elif kind == "associate_right":
        first, (second, third) = input_value
        result = ((first, second), third)
    elif kind == "linear":
        parameter = _parameter(operation, parameters)
        if not isinstance(parameter, LinearParameters):
            raise _error(path, "linear operation referenced non-linear parameters")
        result = jnp.matmul(input_value, parameter.weights) + parameter.bias
    elif kind == "convolution":
        parameter = _parameter(operation, parameters)
        if not isinstance(parameter, ConvolutionParameters):
            raise _error(path, "convolution referenced non-convolution parameters")
        result = _convolution(input_value, parameter.kernel, parameter.bias)
    elif kind == "fixed_convolution":
        attributes = _attributes(operation)
        if attributes.get("kernel") != "nca_perception":
            raise _error(path, "unsupported fixed convolution kernel")
        channels = int(attributes["channels"])
        kernel = nca_perception_kernel(channels, dtype=input_value.dtype)
        bias = jnp.zeros((3 * channels,), dtype=input_value.dtype)
        result = _convolution(input_value, kernel, bias)
    elif kind == "activation":
        if _attributes(operation).get("activation") != "relu":
            raise _error(path, "unsupported activation")
        result = jax.nn.relu(input_value)
    elif kind == "add":
        result = input_value[0] + input_value[1]
    elif kind == "repeat":
        count = int(_attributes(operation)["count"])
        body = operation.children[0]
        result = input_value
        for iteration in range(count):
            result = _apply_operation(
                body,
                parameters,
                result,
                f"{path}.body[{iteration}]",
            )
    else:
        raise _error(path, f"unsupported operation kind {kind!r}")

    return _value(result, operation.output_shape, f"{path}.output")


def apply(
    document: Document,
    parameters: Parameters,
    value: RuntimeValue,
) -> RuntimeValue:
    """Apply a validated document as a pure JAX computation."""

    normalized_parameters = _normalize_parameters(document, parameters)
    return _apply_operation(document.operation, normalized_parameters, value, "operation")


def all_finite(shape: Shape, value: RuntimeValue) -> Array:
    """Return a scalar JAX predicate over every numerical leaf of a value."""

    normalized = _value(value, shape, "value")
    if shape.kind == "unit":
        return jnp.asarray(True)
    if shape.kind in {"scalar", "vector", "grid"}:
        return jnp.all(jnp.isfinite(normalized))
    left, right = shape.children
    return jnp.logical_and(
        all_finite(left, normalized[0]),
        all_finite(right, normalized[1]),
    )
