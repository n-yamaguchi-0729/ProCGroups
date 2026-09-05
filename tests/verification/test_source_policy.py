import importlib.util
from pathlib import Path
import unittest
SOURCE = Path(__file__).resolve().parents[2] / "scripts/verification/generate_manifest.py"
SPEC = importlib.util.spec_from_file_location("policy_gate", SOURCE)
G = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(G)
class PolicyTests(unittest.TestCase):
    def scan(self, text):
        return G.source_policy(G.mask_noncode(text))
    def test_required_autoimplicit_and_comments(self):
        self.assertFalse(self.scan('set_option autoImplicit false\n/- set_option maxHeartbeats 0 -/'))
        self.assertTrue(self.scan('theorem x : True := by trivial'))
    def test_limits_and_suppression_fail(self):
        for command in ['set_option maxHeartbeats 0', 'set_option maxRecDepth 100000',
                        'set_option synthInstance.maxHeartbeats 100000',
                        'set_option linter.style.setOption false', '@[nolint] theorem x : True := by trivial']:
            with self.subTest(command=command):
                self.assertTrue(self.scan('set_option autoImplicit false\n' + command))
    def test_autoimplicit_true_cannot_override_required_false(self):
        self.assertTrue(self.scan('set_option autoImplicit false\nset_option autoImplicit true'))
if __name__ == "__main__":
    unittest.main()
