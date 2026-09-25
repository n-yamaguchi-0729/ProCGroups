# ProCGroups

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library for profinite groups and pro-\(\mathcal C\) groups, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Scope

- Profinite and pro-\(\mathcal C\) groups, finite quotients, inverse systems, and completions
- Free pro-\(\mathcal C\) groups, free products, generation, and presentations
- Pro-\(p\) groups and Golod–Shafarevich criteria
- Completed group algebras, Fox differentials, Reidemeister–Schreier theory, and the Crowell exact sequence

## Usage

The exact Lean and Mathlib revisions are pinned by [`lean-toolchain`](lean-toolchain)
and [`lake-manifest.json`](lake-manifest.json). From the repository root:

```console
lake exe cache get
lake --wfail build
```

Import the complete library with:

```lean
import ProCGroups.All
```

Focused aggregates are also available, for example:

```lean
import ProCGroups.ProP.All
```

## Verification

The [GitHub Actions workflow](.github/workflows/lean.yml) builds the library with
warnings as errors and runs the source audit, NanoDa verification, and Lean kernel replay.

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and preparation of this repository.
Naganori Yamaguchi is the human author and responsible maintainer.

## License

[Apache License 2.0](LICENSE).
