# Verification

The Lean workflow generates a manifest from every maintained physical Lean source and checks reachability, unique module names, the Lean 4.33.0 pin and the exact mathlib revision. Only .git, .lake, scripts/verification, and tests are excluded. Production files must use global autoImplicit false. Proof placeholders, nonstandard axioms, native_decide, unsafe/partial source declarations, nolint, and other source-level option overrides fail the static policy. Static scans do not establish proof safety.

The mandatory serial checks are:

1. Build all manifest roots with warnings as errors.
2. Import at private level and inventory every declaration from all physical manifest modules, including private declarations.
3. Export the complete union of safe declarations using a selector file; verify exact structural name coverage.
4. Run the pinned independent NanoDa checker with only propext, Classical.choice, and Quot.sound permitted. Unpermitted axioms are hard errors; axiom printing has an explicit stdout destination.
5. Replay the imported closure with the official Lean 4.33 kernel in an empty environment.

Each stage needs a zero exit status and its required semantic completion record. There is no skip-stage option. A fresh output directory is required. final.json remains failed/incomplete until every mandatory stage succeeds. Sources, toolchain, Lake configuration, module manifest, checker binaries/artifacts, workflow, policy, and tests are hash-bound. The physical manifest is checked again before and after runtime verification.

Official replay uses the same Lean kernel and skips unsafe/partial constants. The separate inventory rejects sorry and nonstandard transitive axioms, and records excluded declarations. The independent checker has a separate success receipt. None of these checks establishes the correctness of the checker implementation.

## Pinned tools

- Lean: leanprover/lean4:v4.33.0, d8b18978322de05a8f3dba51ef03cf5461676c17.
- mathlib: 6f1ef4e5dd604a435bddba4747b13970cd65d2a1.
- leanprover/lean4export: 15f6055e299ad5b89345e533cc2192f4cc00f659.
- robsimmons/nanoda_lib: 68d5ca9db226849b41a6fff59d796ff19d0a8840.

setup_tools.py fetches the exact checker commits, builds Export with Lake and nanoda_bin with cargo build --release --locked. The checkouts must remain clean. Binary hashes and Rust versions are recorded, since identical source can produce different binary hashes across CI machines. Rust/Cargo come from the Ubuntu runner.

The workflow pins official checkout, lean-action, and upload-artifact actions to verified commits. lean-action is used for Lean installation and mathlib cache acquisition. Its GitHub build-cache option is disabled; the mandatory project build and checker calls belong to verify.py.

## Logs and reproduction

GitHub Actions uploads logs, declaration inventories, manifests, configuration, and JSON receipts for successful and failed runs. The large selected.ndjson export is excluded from the uploaded artifact, but its SHA-256 is recorded; rerunning the same pinned snapshot regenerates it. Artifacts are retained for 14 days.

From the repository root, Python fixtures require only Python 3.11 or newer:

~~~sh
python3 -B -m unittest discover -s tests/verification -p 'test_*.py' -v
~~~

The workflow shows the complete setup and verification commands. Use a new output directory for every attempt. Source-level maintenance scripts predating this verification workflow remain in the repository where present; they are not silently treated as passing current-snapshot checks.

Verification status is specific to a repository commit. Use the matching GitHub Actions run and its logs and receipts to check runtime acceptance of the current source snapshot.
