#!/usr/bin/env python3
"""Small Python-only coverage and fail-closed fixtures; never run Lean or nanoda."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import sys
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[2] / "scripts/verification/verify.py"
sys.path.insert(0, str(SOURCE.parent))
SPEC = importlib.util.spec_from_file_location("portable_verify", SOURCE)
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)


class VerifyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="portable-verify-test-")
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)

    def fixture(self, selected_parts, exported_parts, axioms=()):
        records = [{"meta": {"lean": {"version": "4.33.0", "githash": V.LEAN_COMMIT}}}]
        names = {(): 0}
        def name(parts):
            parts = tuple(parts)
            if parts not in names:
                parent = name(parts[:-1])
                kind, value = parts[-1]
                index = len(names)
                payload = {"pre": parent, "str" if kind == "str" else "i": value}
                records.append({"in": index, kind: payload})
                names[parts] = index
            return names[parts]
        for parts in exported_parts:
            records.append({"thm": {"name": name(parts)}})
        for parts in axioms:
            records.append({"axiom": {"name": name(parts)}})
        path = self.base / "export.ndjson"
        path.write_text("".join(json.dumps(row) + "\n" for row in records))
        inventory = {"selector-" + str(i): {"nameParts": [{k: v} for k, v in parts]}
                     for i, parts in enumerate(selected_parts)}
        return V.export_coverage(path, inventory, list(inventory))

    def args(self):
        return argparse.Namespace(
            package_root=self.base / "package", manifest=self.base / "modules.json",
            output=self.base / "result", exporter_checkout=self.base / "exporter",
            nanoda_checkout=self.base / "nanoda", nanoda_binary=self.base / "nanoda/target/release/nanoda_bin")

    def test_private_numeric_name_coverage(self):
        numeric = (("str", "_private"), ("str", "Owner.Module"), ("num", 7), ("str", "proof"))
        string = (("str", "_private"), ("str", "Owner.Module"), ("str", "7"), ("str", "proof"))
        result = self.fixture([numeric, string], [numeric, string])
        self.assertTrue(result["allSelectedPresent"])
        self.assertEqual(result["selectedDeclarationCount"], 2)
        result = self.fixture([numeric], [string])
        self.assertFalse(result["allSelectedPresent"])

    def test_missing_selected_declaration_and_strict_axioms(self):
        target = (("str", "Owner"), ("str", "target"))
        result = self.fixture([target], [])
        self.assertEqual(result["missingSelectedDeclarations"], ["selector-0"])
        result = self.fixture([target], [target], V.ALLOWED_PARTS)
        self.assertEqual(result["unexpectedAxiomNameParts"], [])
        for spoof in [(("str", "Classical.choice"),), (("str", "Quot.sound"),),
                      (("str", ""), ("str", "propext")), (("str", "sorryAx"),)]:
            with self.subTest(spoof=spoof):
                result = self.fixture([target], [target], [spoof])
                self.assertEqual(result["unexpectedAxiomNameParts"], [spoof])

    def test_missing_inputs_fail_before_any_process_and_leave_failed_final(self):
        runner = V.Pipeline(self.args())
        with patch.object(V.subprocess, "run", side_effect=AssertionError("No subprocess allowed")), \
             patch.object(V.subprocess, "check_output", side_effect=AssertionError("No subprocess allowed")):
            self.assertEqual(runner.execute(), 1)
        final = V.read_json(runner.out / "final.json")
        self.assertFalse(final["passed"])
        self.assertEqual(final["status"], "failed")
        self.assertEqual(final["stages"], [])

    def test_nonzero_build_stops_pipeline_and_records_exit_code(self):
        runner = V.Pipeline(self.args())
        def inputs():
            runner.manifest = {"roots": ["Fixture.All"]}
            runner.lean = Path("/unexecuted/lean")
        with patch.object(runner, "inputs", side_effect=inputs), \
             patch.object(runner, "guard", return_value="fixture-hash"), \
             patch.object(V.subprocess, "run", return_value=subprocess.CompletedProcess([], 7)) as process:
            self.assertEqual(runner.execute(), 1)
        self.assertEqual(process.call_count, 1)
        stage = V.read_json(runner.out / "build.json")
        final = V.read_json(runner.out / "final.json")
        self.assertEqual(stage["exitCode"], 7)
        self.assertFalse(stage["passed"])
        self.assertFalse(final["passed"])
        self.assertEqual([r["stage"] for r in final["stages"]], ["build"])
        self.assertIn("completedUtc", stage)

    def test_missing_output_cannot_mark_zero_exit_stage_passed(self):
        runner = V.Pipeline(self.args())
        runner.out.mkdir()
        with patch.object(runner, "guard", return_value="fixture-hash"), \
             patch.object(V.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)):
            with self.assertRaises(V.VerificationError):
                runner.stage("fixture", ["unexecuted"], artifacts=[runner.out / "missing.json"])
        stage = V.read_json(runner.out / "fixture.json")
        self.assertEqual(stage["exitCode"], 0)
        self.assertFalse(stage["passed"])
        self.assertEqual(stage["status"], "failed")

    def test_nanoda_axiom_printing_has_stdout_destination_and_strict_policy(self):
        runner = V.Pipeline(self.args())
        observed = {}
        def inputs():
            runner.manifest = {"roots": ["Fixture.All"]}
            runner.lean = Path("/unexecuted/lean")
            runner.export_core_dir = Path("/unexecuted/exporter")
            runner.selector_path = runner.out / "safe-union.txt"
        def stage(name, command=None, **kwargs):
            if name == "nanoda":
                observed.update(V.read_json(Path(command[1])))
                # The real config has been generated; never start a kernel in this fixture.
                raise V.VerificationError("fixture stops before nanoda")
        with patch.object(runner, "inputs", side_effect=inputs), \
             patch.object(runner, "capture", return_value="/unexecuted/search"), \
             patch.object(runner, "stage", side_effect=stage), \
             patch.object(V.subprocess, "run", side_effect=AssertionError("No subprocess allowed")):
            self.assertEqual(runner.execute(), 1)
        self.assertTrue(observed["print_axioms"])
        self.assertTrue(observed["pp_to_stdout"])
        self.assertEqual(set(observed["permitted_axioms"]),
                         {"propext", "Classical.choice", "Quot.sound"})
        self.assertTrue(observed["unpermitted_axiom_hard_error"])
        self.assertFalse(observed["unsafe_permit_all_axioms"])
        self.assertTrue(observed["unknown_pp_declar_hard_error"])
        self.assertTrue(observed["print_success_message"])
        self.assertFalse(V.read_json(runner.out / "final.json")["passed"])

    def test_existing_output_is_not_reused_or_overwritten(self):
        runner = V.Pipeline(self.args())
        runner.out.mkdir()
        old = runner.out / "final.json"
        old.write_text('{"historical": true}\n')
        with self.assertRaises(V.VerificationError):
            runner.execute()
        self.assertEqual(old.read_text(), '{"historical": true}\n')


if __name__ == "__main__":
    unittest.main(verbosity=2)
