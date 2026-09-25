# Verification

The [Lean workflow](../workflows/lean.yml) uses the same verification procedure
in each published repository. Run it from the repository root. Its two
repository-specific inputs are:

- `manifest-config.json`: maintained source owners, import roots, and exact
  Lean and mathlib pins.
- `main-declarations.json`: selected public declarations whose names, kinds,
  owner, and specified source modules must remain available.

The other files implement the shared procedure:

1. `generate_manifest.py` inventories every maintained physical Lean source,
   checks its import reachability and source policy, and records source hashes.
2. `setup_tools.py` obtains and builds pinned `lean4export` and NanoDa revisions.
   The workflow obtains the pinned Lean toolchain and mathlib cache first.
3. `verify.py` runs the mandatory build with warnings as errors, inventories
   every declaration (including private declarations), selects and exports the
   safe declaration union, checks exact export coverage, checks it with NanoDa,
   and replays the import closure with the official Lean kernel. `Inventory.lean`,
   `ExportSelected.lean`, and `ReplayKernel.lean` implement its Lean stages.
4. `check_main_declarations.py` checks the selected public API against the
   audited inventory and the successful verification receipts. This checks
   declaration presence and kind; it does not compare theorem statements.
5. The workflow checks whitespace and uploads logs, manifests, and receipts
   even if a stage fails.

The runtime stages run in order: build, inventory, selection, export, coverage,
NanoDa, and kernel replay. Every stage must pass. Use a fresh output directory
for each local attempt and follow the commands in the workflow; a static source
audit alone does not verify proofs. The workflow keeps its artifacts for 14 days.
