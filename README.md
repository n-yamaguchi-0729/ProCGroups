# ProCGroups (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Developed as part of [NYLL](https://github.com/n-yamaguchi-0729/NYLL), this Lean library studies profinite and pro-C groups,
from finite quotients and completions to free groups, Golod–Shafarevich criteria
and completed Crowell sequences. The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/pro-c-groups/) explains the main constructions
and selected theorems, with links to their proofs.

## Scope

The library covers finite quotients, completions, free pro-\(\mathcal C\) groups, pro-\(p\) groups,
and Golod--Shafarevich criteria. It also develops completed group algebras,
Fox differentials, Reidemeister--Schreier theory, and Crowell exact sequences.

The [full Tate module](Nyll/ProCGroups/Abelian/FullTateModule.lean) is also
constructed as an inverse limit of torsion subgroups.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Free pro-\(\mathcal C\) groups](Nyll/ProCGroups/FreeProC/Basic.lean) | The universal property for a free pro-\(\mathcal C\) group on a topological generating space. |
| [Weighted Golod--Shafarevich criterion](Nyll/ProCGroups/GolodShafarevich/WeightedFiniteCriterion.lean) | A nonpositive weighted Golod--Shafarevich polynomial forces the target of a finite pro-\(p\) presentation to be infinite. |
| [Discrete Crowell sequence](Nyll/ProCGroups/CrowellExactSequence/Discrete/MainTheorem.lean) | Exactness of the discrete four-term Crowell sequence for a surjective group homomorphism. |
| [Completed Crowell sequence](Nyll/ProCGroups/CrowellExactSequence/Profinite/MainTheorem.lean) | Exactness of the separated completed Crowell sequence over pro-\(\mathcal C\) integer coefficients under the stated formation and source hypotheses. |
| [Pontryagin biduality](Nyll/ProCGroups/Abelian/ProfiniteBidual.lean) | Biduality for finite and profinite abelian groups. |
| [Recognition of the profinite integers](Nyll/ProCGroups/Completion/ProfiniteIntegerRecognition.lean) | A topological generator and finite quotients of every positive order characterize the profinite integers. |

## Public API

Complete library:

```lean
import Nyll.ProCGroups.All
```

Focused imports:

```lean
import Nyll.ProCGroups.FreeProC.All
import Nyll.ProCGroups.ProP.All
import Nyll.ProCGroups.GolodShafarevich.All
import Nyll.ProCGroups.CrowellExactSequence.All
```

## Build

The repository pins the Lean toolchain and dependencies in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).
The dependency lock is in [`lake-manifest.json`](lake-manifest.json).
From the repository root:

```console
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
