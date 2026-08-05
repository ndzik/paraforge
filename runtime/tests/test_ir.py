from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import unittest

from jsonschema import Draft202012Validator, validate

from paraforge_runtime.ir import (
    ValidationError,
    grid,
    load_document,
    parse_document,
    loads_document,
)


ROOT = Path(__file__).resolve().parents[2]
GOLDEN = ROOT / "examples" / "nca.json"
SCHEMA = ROOT / "schema" / "paraforge-architecture-v1.schema.json"


def raw_golden() -> dict[str, object]:
    return json.loads(GOLDEN.read_text(encoding="utf-8"))


def find_operation(operation: dict[str, object], kind: str) -> dict[str, object]:
    if operation.get("type") == kind:
        return operation
    for field in ("body", "first", "later", "left", "right"):
        child = operation.get(field)
        if isinstance(child, dict):
            try:
                return find_operation(child, kind)
            except LookupError:
                pass
    raise LookupError(kind)


def parameter_references(operation) -> list[int]:
    direct = [] if operation.parameter is None else [operation.parameter]
    if operation.kind == "repeat":
        count = dict(operation.attributes)["count"]
        return parameter_references(operation.children[0]) * count
    result = direct
    for child in operation.children:
        result.extend(parameter_references(child))
    return result


class GoldenDocumentTests(unittest.TestCase):
    def test_golden_nca_is_valid(self) -> None:
        document = load_document(GOLDEN)

        self.assertEqual(document.schema, "paraforge-architecture")
        self.assertEqual(document.version, 1)
        self.assertEqual(document.input_shape, grid(16, 16, 4))
        self.assertEqual(document.output_shape, grid(16, 16, 4))
        self.assertEqual(len(document.parameters), 2)
        self.assertEqual(document.parameters[0].kind, "linear")
        self.assertEqual(document.parameters[0].dimensions, (16, 4))
        self.assertEqual(document.parameters[1].dimensions, (12, 16))
        self.assertEqual(document.operation.kind, "repeat")
        self.assertEqual(dict(document.operation.attributes)["count"], 4)
        self.assertEqual(
            parameter_references(document.operation),
            [1, 0, 1, 0, 1, 0, 1, 0],
        )

    def test_schema_file_is_closed_version_one_json_schema(self) -> None:
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        document = raw_golden()

        Draft202012Validator.check_schema(schema)
        validate(document, schema)
        self.assertEqual(schema["properties"]["version"], {"const": 1})
        self.assertFalse(schema["additionalProperties"])
        self.assertIn("operation", schema["$defs"])


class ConstructorCoverageTests(unittest.TestCase):
    @staticmethod
    def document(operation, input_shape, output_shape, parameters=None):
        return {
            "schema": "paraforge-architecture",
            "version": 1,
            "input": input_shape,
            "output": output_shape,
            "parameters": [] if parameters is None else parameters,
            "operation": operation,
        }

    def test_trainable_convolution_is_validated(self) -> None:
        input_shape = {"type": "grid", "height": 8, "width": 8, "channels": 2}
        output_shape = {"type": "grid", "height": 8, "width": 8, "channels": 5}
        parameter = {
            "id": 0,
            "kind": "convolution",
            "kernel_height": 3,
            "kernel_width": 3,
            "input_channels": 2,
            "output_channels": 5,
        }
        operation = {
            "type": "convolution",
            "height": 8,
            "width": 8,
            "kernel_height": 3,
            "kernel_width": 3,
            "input_channels": 2,
            "output_channels": 5,
            "parameter": 0,
        }

        document = parse_document(
            self.document(operation, input_shape, output_shape, [parameter])
        )

        self.assertEqual(document.operation.kind, "convolution")
        self.assertEqual(dict(document.operation.attributes)["boundary"], "zero")
        self.assertEqual(dict(document.operation.attributes)["stride"], 1)

    def test_all_structural_generators_are_validated(self) -> None:
        first = {"type": "grid", "height": 2, "width": 3, "channels": 4}
        second = {"type": "vector", "features": 5}
        third = {"type": "scalar"}
        product_first_second = {"type": "product", "left": first, "right": second}
        product_second_third = {"type": "product", "left": second, "right": third}
        cases = (
            ("discard", first, {"type": "unit"}),
            (
                "swap",
                product_first_second,
                {"type": "product", "left": second, "right": first},
            ),
            (
                "associate_left",
                {"type": "product", "left": product_first_second, "right": third},
                {"type": "product", "left": first, "right": product_second_third},
            ),
            (
                "associate_right",
                {"type": "product", "left": first, "right": product_second_third},
                {"type": "product", "left": product_first_second, "right": third},
            ),
        )

        for kind, input_shape, output_shape in cases:
            with self.subTest(kind=kind):
                operation = {"type": kind, "input": input_shape, "output": output_shape}
                document = parse_document(
                    self.document(operation, input_shape, output_shape)
                )
                self.assertEqual(document.operation.kind, kind)


class StrictValidationTests(unittest.TestCase):
    def assert_invalid(self, value: object, message: str) -> None:
        with self.assertRaisesRegex(ValidationError, message):
            parse_document(value)

    def test_unknown_version_is_rejected(self) -> None:
        raw = raw_golden()
        raw["version"] = 2
        self.assert_invalid(raw, "unsupported schema version 2")

    def test_unknown_top_level_field_is_rejected(self) -> None:
        raw = raw_golden()
        raw["jax_device"] = "gpu"
        self.assert_invalid(raw, "unknown fields: jax_device")

    def test_duplicate_json_field_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValidationError, "duplicate JSON field 'version'"):
            loads_document(
                '{"schema":"paraforge-architecture","version":1,"version":1}'
            )

    def test_unknown_operation_is_rejected(self) -> None:
        raw = raw_golden()
        raw["operation"] = {"type": "residual"}
        self.assert_invalid(raw, "unknown operation 'residual'")

    def test_noncanonical_parameter_id_is_rejected(self) -> None:
        raw = raw_golden()
        raw["parameters"][1]["id"] = 0
        self.assert_invalid(raw, "expected canonical external parameter id 1")

    def test_unknown_parameter_reference_is_rejected(self) -> None:
        raw = raw_golden()
        hidden = find_operation(raw["operation"], "linear")
        hidden["parameter"] = 9
        self.assert_invalid(raw, "unknown external parameter id 9")

    def test_mistyped_parameter_reference_is_rejected(self) -> None:
        raw = raw_golden()
        hidden = find_operation(raw["operation"], "linear")
        hidden["parameter"] = 0
        self.assert_invalid(raw, "expected linear\\(12, 16\\)")

    def test_sequential_shape_mismatch_is_rejected(self) -> None:
        raw = raw_golden()
        activation = find_operation(raw["operation"], "activation")
        activation["channels"] = 15
        self.assert_invalid(raw, "sequential intermediate shapes do not match")

    def test_parallel_product_mismatch_is_rejected(self) -> None:
        raw = raw_golden()
        identity = find_operation(raw["operation"], "identity")
        identity["shape"]["channels"] = 5
        self.assert_invalid(raw, "sequential intermediate shapes do not match")

    def test_non_endomorphic_repeat_is_rejected(self) -> None:
        raw = raw_golden()
        fixed_convolution = find_operation(raw["operation"], "fixed_convolution")
        raw["operation"]["body"] = deepcopy(fixed_convolution)
        self.assert_invalid(raw, "repeat body must be an endomorphism")

    def test_fixed_kernel_boundary_is_rejected(self) -> None:
        raw = raw_golden()
        fixed_convolution = find_operation(raw["operation"], "fixed_convolution")
        fixed_convolution["kernel"]["boundary"] = "wrap"
        self.assert_invalid(raw, "requires zero padding")

    def test_document_output_mismatch_is_rejected(self) -> None:
        raw = raw_golden()
        raw["output"]["channels"] = 5
        self.assert_invalid(raw, "does not match the operation output shape")

    def test_boolean_dimension_is_not_an_integer(self) -> None:
        raw = raw_golden()
        raw["input"]["height"] = True
        self.assert_invalid(raw, "expected an integer")


if __name__ == "__main__":
    unittest.main()
