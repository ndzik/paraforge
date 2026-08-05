from __future__ import annotations

from pathlib import Path

import jax
import jax.numpy as jnp
import pytest

from paraforge_runtime.ir import (
    Document,
    Operation,
    ParameterSpec,
    SCALAR,
    UNIT,
    grid,
    load_document,
    product,
    vector,
)
from paraforge_runtime.jax_interpreter import (
    ConvolutionParameters,
    ExecutionError,
    LinearParameters,
    all_finite,
    apply,
    initialize,
    nca_perception_kernel,
)


ROOT = Path(__file__).resolve().parents[2]
GOLDEN = ROOT / "examples" / "nca.json"


def document(
    operation: Operation,
    parameters: tuple[ParameterSpec, ...] = (),
) -> Document:
    return Document(
        "paraforge-architecture",
        1,
        operation.input_shape,
        operation.output_shape,
        parameters,
        operation,
    )


def assert_close(actual, expected) -> None:
    assert bool(jnp.allclose(actual, expected, rtol=1e-6, atol=1e-6))


def manual_hwc_correlation(value, kernel, bias):
    height, width, _ = value.shape
    kernel_height, kernel_width, _, output_channels = kernel.shape
    before_height = (kernel_height - 1) // 2
    before_width = (kernel_width - 1) // 2
    padded = jnp.pad(
        value,
        (
            (before_height, kernel_height - 1 - before_height),
            (before_width, kernel_width - 1 - before_width),
            (0, 0),
        ),
    )
    result = []
    for row in range(height):
        result_row = []
        for column in range(width):
            patch = padded[
                row : row + kernel_height,
                column : column + kernel_width,
                :,
            ]
            result_row.append(
                [
                    jnp.sum(patch * kernel[:, :, :, channel]) + bias[channel]
                    for channel in range(output_channels)
                ]
            )
        result.append(result_row)
    return jnp.asarray(result)


class TestInitialization:
    def test_is_deterministic_and_indexed_by_external_id(self) -> None:
        architecture = load_document(GOLDEN)
        key = jax.random.key(42)

        first = initialize(architecture, key)
        second = initialize(architecture, key)
        different = initialize(architecture, jax.random.key(43))

        assert len(first) == 2
        assert isinstance(first[0], LinearParameters)
        assert first[0].weights.shape == (16, 4)
        assert first[0].bias.shape == (4,)
        assert first[1].weights.shape == (12, 16)
        assert first[1].bias.shape == (16,)
        assert first[0].weights.dtype == jnp.float32
        assert bool(jnp.array_equal(first[0].weights, second[0].weights))
        assert bool(jnp.array_equal(first[1].weights, second[1].weights))
        assert not bool(jnp.array_equal(first[0].weights, different[0].weights))
        assert bool(jnp.all(first[0].bias == 0))
        assert bool(jnp.all(first[1].bias == 0))

        unused_parameter_operation = Operation(
            "identity",
            architecture.input_shape,
            architecture.input_shape,
        )
        only_first = document(
            unused_parameter_operation,
            (architecture.parameters[0],),
        )
        first_in_shorter_context = initialize(only_first, key)[0]
        assert bool(
            jnp.array_equal(first[0].weights, first_in_shorter_context.weights)
        )

    def test_convolution_initialization_uses_hwio_layout(self) -> None:
        shape = grid(4, 5, 2)
        operation = Operation("identity", shape, shape)
        specification = ParameterSpec(0, "convolution", (3, 2, 2, 7))

        values = initialize(document(operation, (specification,)), jax.random.key(0))

        assert isinstance(values[0], ConvolutionParameters)
        assert values[0].kernel.shape == (3, 2, 2, 7)
        assert values[0].bias.shape == (7,)
        assert bool(jnp.all(values[0].bias == 0))

    def test_rejects_non_floating_parameter_dtype(self) -> None:
        architecture = load_document(GOLDEN)

        with pytest.raises(ExecutionError, match="parameter dtype must be floating"):
            initialize(architecture, jax.random.key(0), dtype=jnp.int32)


class TestNumericalPrimitives:
    def test_linear_is_pointwise_over_the_final_axis(self) -> None:
        input_shape = grid(1, 2, 2)
        output_shape = grid(1, 2, 3)
        specification = ParameterSpec(0, "linear", (2, 3))
        operation = Operation("linear", input_shape, output_shape, parameter=0)
        parameters = (
            LinearParameters(
                jnp.asarray([[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]]),
                jnp.asarray([0.5, -0.5, 1.0]),
            ),
        )
        value = jnp.asarray([[[1.0, 2.0], [-1.0, 3.0]]])
        expected = jnp.matmul(value, parameters[0].weights) + parameters[0].bias

        result = apply(document(operation, (specification,)), parameters, value)

        assert_close(result, expected)

    def test_convolution_is_explicit_same_shape_cross_correlation(self) -> None:
        input_shape = grid(2, 3, 1)
        output_shape = grid(2, 3, 1)
        specification = ParameterSpec(0, "convolution", (2, 2, 1, 1))
        operation = Operation("convolution", input_shape, output_shape, parameter=0)
        kernel = jnp.asarray([[[[1.0]], [[2.0]]], [[[3.0]], [[4.0]]]])
        bias = jnp.asarray([0.25])
        parameters = (ConvolutionParameters(kernel, bias),)
        value = jnp.arange(1.0, 7.0).reshape(2, 3, 1)
        expected = manual_hwc_correlation(value, kernel, bias)

        result = apply(document(operation, (specification,)), parameters, value)

        assert result.shape == value.shape
        assert_close(result, expected)

    def test_fixed_nca_perception_has_frozen_interleaved_filters(self) -> None:
        kernel = nca_perception_kernel(2)
        identity = jnp.asarray(
            [[0.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 0.0]]
        )
        sobel_x = jnp.asarray(
            [[-1.0, 0.0, 1.0], [-2.0, 0.0, 2.0], [-1.0, 0.0, 1.0]]
        ) / 8.0
        sobel_y = jnp.asarray(
            [[-1.0, -2.0, -1.0], [0.0, 0.0, 0.0], [1.0, 2.0, 1.0]]
        ) / 8.0

        assert kernel.shape == (3, 3, 2, 6)
        assert_close(kernel[:, :, 0, 0], identity)
        assert_close(kernel[:, :, 0, 1], sobel_x)
        assert_close(kernel[:, :, 0, 2], sobel_y)
        assert_close(kernel[:, :, 1, 3], identity)
        assert_close(kernel[:, :, 1, 4], sobel_x)
        assert_close(kernel[:, :, 1, 5], sobel_y)
        assert bool(jnp.all(kernel[:, :, 0, 3:] == 0))
        assert bool(jnp.all(kernel[:, :, 1, :3] == 0))

        input_shape = grid(3, 4, 2)
        output_shape = grid(3, 4, 6)
        operation = Operation(
            "fixed_convolution",
            input_shape,
            output_shape,
            attributes=(
                ("kernel", "nca_perception"),
                ("channels", 2),
                ("boundary", "zero"),
            ),
        )
        value = jnp.arange(24.0).reshape(3, 4, 2)
        expected = manual_hwc_correlation(value, kernel, jnp.zeros((6,)))

        result = apply(document(operation), (), value)

        assert_close(result, expected)

    def test_relu_and_add_have_direct_meanings(self) -> None:
        shape = grid(1, 2, 1)
        activation = Operation(
            "activation",
            shape,
            shape,
            attributes=(("activation", "relu"),),
        )
        add = Operation("add", product(shape, shape), shape)
        left = jnp.asarray([[[-2.0], [3.0]]])
        right = jnp.asarray([[[5.0], [-1.0]]])

        activated = apply(document(activation), (), left)
        summed = apply(document(add), (), (left, right))

        assert_close(activated, jnp.asarray([[[0.0], [3.0]]]))
        assert_close(summed, left + right)


class TestStructuralOperations:
    def test_structural_generators_preserve_their_tuple_meanings(self) -> None:
        scalar = jnp.asarray(2.0)
        values = jnp.asarray([3.0, 4.0])
        scalar_vector = product(SCALAR, vector(2))

        identity = Operation("identity", SCALAR, SCALAR)
        copy = Operation("copy", SCALAR, product(SCALAR, SCALAR))
        discard = Operation("discard", SCALAR, UNIT)
        swap = Operation("swap", scalar_vector, product(vector(2), SCALAR))
        associate_left = Operation(
            "associate_left",
            product(scalar_vector, UNIT),
            product(SCALAR, product(vector(2), UNIT)),
        )
        associate_right = Operation(
            "associate_right",
            product(SCALAR, product(vector(2), UNIT)),
            product(scalar_vector, UNIT),
        )

        assert_close(apply(document(identity), (), scalar), scalar)
        copied = apply(document(copy), (), scalar)
        assert_close(copied[0], scalar)
        assert_close(copied[1], scalar)
        assert apply(document(discard), (), scalar) == ()
        swapped = apply(document(swap), (), (scalar, values))
        assert_close(swapped[0], values)
        assert_close(swapped[1], scalar)
        associated = apply(document(associate_left), (), ((scalar, values), ()))
        assert_close(associated[0], scalar)
        assert_close(associated[1][0], values)
        assert associated[1][1] == ()
        restored = apply(document(associate_right), (), associated)
        assert_close(restored[0][0], scalar)
        assert_close(restored[0][1], values)
        assert restored[1] == ()

    def test_sequential_and_parallel_agree_with_direct_composition(self) -> None:
        shape = grid(1, 1, 1)
        specifications = (
            ParameterSpec(0, "linear", (1, 1)),
            ParameterSpec(1, "linear", (1, 1)),
        )
        parameters = (
            LinearParameters(jnp.asarray([[2.0]]), jnp.asarray([1.0])),
            LinearParameters(jnp.asarray([[3.0]]), jnp.asarray([-1.0])),
        )
        first = Operation("linear", shape, shape, parameter=0)
        later = Operation("linear", shape, shape, parameter=1)
        sequential = Operation(
            "sequential",
            shape,
            shape,
            children=(first, later),
        )
        parallel = Operation(
            "parallel",
            product(shape, shape),
            product(shape, shape),
            children=(first, later),
        )
        left_value = jnp.asarray([[[2.0]]])
        right_value = jnp.asarray([[[5.0]]])

        sequential_result = apply(
            document(sequential, specifications),
            parameters,
            left_value,
        )
        direct_sequential = apply(
            document(later, specifications),
            parameters,
            apply(document(first, specifications), parameters, left_value),
        )
        parallel_result = apply(
            document(parallel, specifications),
            parameters,
            (left_value, right_value),
        )
        direct_parallel = (
            apply(document(first, specifications), parameters, left_value),
            apply(document(later, specifications), parameters, right_value),
        )

        assert_close(sequential_result, direct_sequential)
        assert_close(parallel_result[0], direct_parallel[0])
        assert_close(parallel_result[1], direct_parallel[1])

    def test_repeat_reuses_one_parameter_value(self) -> None:
        shape = grid(1, 1, 1)
        specification = ParameterSpec(0, "linear", (1, 1))
        body = Operation("linear", shape, shape, parameter=0)
        repeated = Operation(
            "repeat",
            shape,
            shape,
            children=(body,),
            attributes=(("count", 3),),
        )
        parameters = (
            LinearParameters(jnp.asarray([[2.0]]), jnp.asarray([1.0])),
        )

        initial = jnp.asarray([[[1.0]]])
        result = apply(
            document(repeated, (specification,)),
            parameters,
            initial,
        )
        repeated_zero = Operation(
            "repeat",
            shape,
            shape,
            children=(body,),
            attributes=(("count", 0),),
        )
        zero_result = apply(
            document(repeated_zero, (specification,)),
            parameters,
            initial,
        )

        assert_close(result, jnp.asarray([[[15.0]]]))
        assert_close(zero_result, initial)

    def test_runtime_boundaries_reject_bad_values_and_parameters(self) -> None:
        shape = grid(1, 1, 1)
        specification = ParameterSpec(0, "linear", (1, 1))
        operation = Operation("linear", shape, shape, parameter=0)
        architecture = document(operation, (specification,))
        valid_parameters = (
            LinearParameters(jnp.ones((1, 1)), jnp.zeros((1,))),
        )

        with pytest.raises(ExecutionError, match="expected array shape"):
            apply(architecture, valid_parameters, jnp.ones((2, 1, 1)))
        with pytest.raises(ExecutionError, match="expected a floating numerical dtype"):
            apply(
                architecture,
                valid_parameters,
                jnp.ones((1, 1, 1), dtype=jnp.int32),
            )
        with pytest.raises(ExecutionError, match="expected shape"):
            apply(
                architecture,
                (LinearParameters(jnp.ones((2, 1)), jnp.zeros((1,))),),
                jnp.ones((1, 1, 1)),
            )
        with pytest.raises(ExecutionError, match="expected a floating dtype"):
            apply(
                architecture,
                (LinearParameters(jnp.ones((1, 1), dtype=jnp.int32), jnp.zeros((1,))),),
                jnp.ones((1, 1, 1)),
            )


class TestExportedNCA:
    def test_rollout_is_deterministic_finite_and_jittable(self) -> None:
        architecture = load_document(GOLDEN)
        parameters = initialize(architecture, jax.random.key(2026))
        seed = jnp.zeros((16, 16, 4), dtype=jnp.float32)
        seed = seed.at[8, 8, 0].set(1.0)

        first = apply(architecture, parameters, seed)
        second = apply(architecture, parameters, seed)
        compiled = jax.jit(lambda p, value: apply(architecture, p, value))
        jitted = compiled(parameters, seed)

        assert first.shape == (16, 16, 4)
        assert bool(all_finite(architecture.output_shape, first))
        assert bool(jnp.array_equal(first, second))
        assert_close(jitted, first)

    def test_repeat_equals_four_explicit_shared_steps(self) -> None:
        architecture = load_document(GOLDEN)
        parameters = initialize(architecture, jax.random.key(9))
        seed = jnp.zeros((16, 16, 4), dtype=jnp.float32)
        seed = seed.at[7, 8, 0].set(1.0)
        repeat = architecture.operation
        assert repeat.kind == "repeat"
        step = repeat.children[0]
        step_document = document(step, architecture.parameters)

        explicit = seed
        for _ in range(4):
            explicit = apply(step_document, parameters, explicit)

        rolled_out = apply(architecture, parameters, seed)

        assert_close(rolled_out, explicit)

    def test_elaborated_step_is_delta_plus_identity(self) -> None:
        architecture = load_document(GOLDEN)
        parameters = initialize(architecture, jax.random.key(11))
        seed = jnp.zeros((16, 16, 4), dtype=jnp.float32)
        seed = seed.at[8, 8, 1].set(1.0)
        step = architecture.operation.children[0]
        assert step.kind == "sequential"
        residual_tail = step.children[1]
        parallel = residual_tail.children[0]
        delta = parallel.children[0]
        step_document = document(step, architecture.parameters)
        delta_document = document(delta, architecture.parameters)

        actual = apply(step_document, parameters, seed)
        expected = apply(delta_document, parameters, seed) + seed

        assert_close(actual, expected)
