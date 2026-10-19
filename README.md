# ProCGroups (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Developed as part of [NYLL](https://github.com/n-yamaguchi-0729/NYLL), this Lean library studies profinite and pro-C groups,
from finite quotients and completions to free groups, Golod–Shafarevich criteria
and completed Crowell sequences. The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/pro-c-groups/) explains the main constructions
and selected theorems, with links to their proofs.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Free pro-\(\mathcal C\) groups](Nyll/ProCGroups/FreeProC/Basic.lean) | The universal property for a free pro-\(\mathcal C\) group on a topological generating space. |
| [Weighted Golod--Shafarevich criterion](Nyll/ProCGroups/GolodShafarevich/WeightedFiniteCriterion.lean) | A nonpositive weighted Golod--Shafarevich polynomial forces the target of a finite pro-\(p\) presentation to be infinite. |
| [Completed Crowell sequence](Nyll/ProCGroups/CrowellExactSequence/Profinite/MainTheorem.lean) | Exactness of the separated completed Crowell sequence over pro-\(\mathcal C\) integer coefficients under the stated formation and source hypotheses. |
| [Pontryagin biduality](Nyll/ProCGroups/Abelian/ProfiniteBidual.lean) | Biduality for finite and profinite abelian groups. |

## Public API

Use [leanprover/lean4:v4.35.0-rc2](lean-toolchain) and the Mathlib revision pinned in
[lake-manifest.json](lake-manifest.json). Add this dependency to your project’s
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/ProCGroups.git"
rev = "main"
```

Run `lake update Nyll`, then commit your generated lake-manifest.json to retain
the resolved revisions. Import the library in a Lean file:

```lean
import Nyll.ProCGroups.All
```

The standalone distributions share the package name Nyll. Choose one distribution;
for several libraries together, use [NYLL](https://github.com/n-yamaguchi-0729/NYLL).

To build a checkout of this repository, run from its root:

```sh
lake exe cache get
lake --wfail build
```

## Verification

[CI](.github/workflows/lean.yml) checks the import closure, builds with
warnings as errors, audits declarations, and verifies proofs with NanoDa
and the Lean kernel. The [public API contract](.github/verification/main-declarations.json)
checks the named declarations and their source modules.

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.

## License

<!-- nyll-publication:credits:begin -->
Apache License 2.0. See [LICENSE](LICENSE).

Included adaptations from [Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem) retain their source-specific copyrights and authors.
The included-file inventories and preserved upstream notices are in [NOTICE](NOTICE).
<!-- nyll-publication:credits:end -->
