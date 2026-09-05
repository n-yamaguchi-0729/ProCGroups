#!/usr/bin/env python3
"""Tiny meaningful fixtures only: no Lean, Lake, builds, network, or public-package runs."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parents[2] / "scripts/verification"
spec = importlib.util.spec_from_file_location("manifest_gate", HERE / "generate_manifest.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
REV = "6f1ef4e5dd604a435bddba4747b13970cd65d2a1"


class GateFixtures(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lean-manifest-fixture-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config = {
            "owners": {"PCG": ["PCG"], "Aux": ["Aux"]},
            "roots": ["PCG.All", "Aux.All"],
            "leanToolchain": "leanprover/lean4:v4.33.0",
            "mathlibRevision": REV,
            "excludedDirectories": [".git", ".lake", "submission", "Challenge"],
        }
        self.lake = f'''name = "fixture"
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{REV}"
[[lean_lib]]
name = "PCG.All"
srcDir = "src"
globs = ["PCG.+"]
[[lean_lib]]
name = "Aux.All"
srcDir = "src"
globs = ["Aux.+"]
'''
        self.put("lakefile.toml", self.lake)
        self.put("lean-toolchain", self.config["leanToolchain"] + "\n")
        self.lock = {"packages": [
            {"name": "mathlib", "type": "git", "rev": REV,
             "url": "https://github.com/leanprover-community/mathlib4", "inputRev": REV},
            {"name": "inherited", "type": "git", "rev": "a" * 40, "inputRev": "main", "inherited": True},
        ]}
        self.save_lock()
        self.put("src/PCG/All.lean", "public import PCG.Basic\n")
        self.put("src/PCG/Basic.lean", 'import Mathlib.Data.Nat.Basic\n/- outer sorry /- axiom -/ -/\ndef text := "admit native_decide"\ntheorem ok : True := by trivial\n')
        self.put("src/Aux/All.lean", "import Aux.Core\n")
        self.put("src/Aux/Core.lean", "public meta import PCG.Basic\nimport Std.Data.HashMap\n")
        self.put(".lake/packages/bad/Bad.lean", "sorry\n")
        self.put("submission/Challenge.lean", "axiom excluded : False\n")
        self.put("Challenge/Bad.lean", "native_decide\n")

    def put(self, path, text):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text, encoding="utf-8")

    def save_lock(self):
        self.put("lake-manifest.json", json.dumps(self.lock))

    def run_gate(self):
        return gate.analyze(self.root, self.config)

    def kinds(self):
        return {row["kind"] for row in self.run_gate()[1]["errors"]}

    def test_valid_all_sources_and_symbolic_inherited_input_rev(self):
        manifest, report = self.run_gate()
        self.assertTrue(report["staticPassed"], report["errors"])
        self.assertEqual(len(manifest["moduleRows"]), 4)
        self.assertEqual(report["ownerModuleCounts"], {"Aux": 2, "PCG": 2})
        self.assertFalse(report["proofSafetyEstablished"])
        self.assertNotIn("repairedModules", manifest)

    def test_optional_repair_subset(self):
        self.config["repairedModules"] = ["PCG.Basic"]
        self.assertEqual(self.run_gate()[0]["repairedModules"], ["PCG.Basic"])

    def test_missing_local_import(self):
        self.put("src/PCG/Basic.lean", "import PCG.Typo\n")
        self.assertIn("unresolved-local-import", self.kinds())

    def test_pcg_boundary_and_cycle(self):
        self.put("src/PCG/Basic.lean", "import Aux.Core\n")
        self.assertIn("pcg-import-policy", self.kinds())
        self.assertIn("import-cycle", self.kinds())

    def test_new_unimported_source_is_not_omitted(self):
        self.put("src/PCG/Orphan.lean", "theorem orphan : True := by trivial\n")
        manifest, report = self.run_gate()
        self.assertIn("PCG.Orphan", manifest["moduleRows"])
        self.assertIn("unreachable-sources", {x["kind"] for x in report["errors"]})

    def test_all_forbidden_tokens_outside_comments_and_strings(self):
        for token in ["sorry", "admit", "native_decide", "axiom", "constant"]:
            with self.subTest(token=token):
                self.put("src/PCG/Basic.lean", f"private {token} bad : False\n")
                self.assertIn("forbidden-source-token", self.kinds())

    def test_fixed_toolchain(self):
        self.put("lean-toolchain", "leanprover/lean4:stable\n")
        self.assertIn("lean-pin", self.kinds())

    def test_direct_mathlib_pin(self):
        self.put("lakefile.toml", self.lake.replace(REV, "main"))
        self.assertIn("mathlib-require-pin", self.kinds())

    def test_resolved_git_commit_required(self):
        self.lock["packages"][1]["rev"] = "main"
        self.save_lock()
        self.assertIn("lock-revision", self.kinds())

    def test_excluded_module_cannot_be_imported(self):
        self.put("src/Aux/Core.lean", "import Challenge.Bad\n")
        self.assertIn("unresolved-local-import", self.kinds())

    def test_unowned_physical_source_fails(self):
        self.put("Other/Unowned.lean", "theorem local : True := by trivial\n")
        self.assertIn("source-mapping", self.kinds())

    def test_lake_lean_configuration_is_explicitly_unsupported(self):
        self.put("lakefile.lean", "import Lake\n")
        with self.assertRaisesRegex(ValueError, "unsupported"):
            self.run_gate()

    def test_multiline_import_fails_explicitly(self):
        self.put("src/PCG/Basic.lean", "import\n  Mathlib.Data.Nat.Basic\n")
        self.assertIn("import-unsupported", self.kinds())

    def test_duplicate_json_keys_rejected(self):
        self.put("bad.json", '{"roots": [], "roots": []}')
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            gate.load_json(self.root / "bad.json")

    def test_cli_existing_manifest_omission_fails_without_writing_new_manifest(self):
        self.put("config.json", json.dumps(self.config))
        manifest, _ = self.run_gate()
        del manifest["moduleRows"]["PCG.Basic"]
        self.put("old.json", json.dumps(manifest))
        with contextlib.redirect_stdout(io.StringIO()):
            code = gate.main(["--root", str(self.root), "--config", str(self.root / "config.json"),
                              "--manifest", str(self.root / "new.json"), "--report", str(self.root / "report.json"),
                              "--check-manifest", str(self.root / "old.json")])
        self.assertEqual(code, 1)
        self.assertFalse((self.root / "new.json").exists())
        self.assertFalse(json.loads((self.root / "report.json").read_text())["staticPassed"])


if __name__ == "__main__":
    unittest.main()
