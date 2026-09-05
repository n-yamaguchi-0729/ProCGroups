# ProCGroups

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library for profinite groups and pro-\(\mathcal C\) groups,
with Mathlib as its external Lean dependency.
Documentation and the library catalog: [Yamaguchi Lean 4 Library](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/).

## Contents

- Profinite and pro-\(\mathcal C\) groups, finite quotients, and inverse limits.
- Free pro-\(\mathcal C\) groups, free products, finite generation, and presentations.
- Completed group algebras, Fox differentials, Reidemeister–Schreier theory,
  and the Crowell exact sequence.

## Build and use

Use **Lean 4.33.0** and the checked-in `lake-manifest.json`, which pins Mathlib
to `6f1ef4e5dd604a435bddba4747b13970cd65d2a1`. From the repository root:

```console
lake exe cache get
lake --wfail build
```

The default build covers all maintained modules. Import the whole library:

```lean
import ProCGroups
```

Or use a focused aggregate:

```lean
import ProCGroups.CrowellExactSequence.All
```

Folder aggregates now use `.All`; the top-level `import ProCGroups` is preserved.

## Verification

The [Lean workflow](.github/workflows/lean.yml) builds with warnings as errors,
audits declaration dependencies against `propext`, `Classical.choice`, and
`Quot.sound`, and runs NanoDa and the official Lean kernel replay.
Workflow artifacts contain the logs and receipts; check the run's commit and
result in GitHub Actions.

This library was developed with AI assistance by a non-specialist; please review the material independently.

## License

Apache License 2.0. See [LICENSE](LICENSE).
