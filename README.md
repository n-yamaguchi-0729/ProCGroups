# ProCGroups (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4.35.0-rc2 library for profinite groups and pro-\(\mathcal C\) groups.

This library is extracted from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).
Bundled dependencies use the same `Nyll` imports as the complete library.

## Scope

The library covers finite quotients, completions, free pro-\(\mathcal C\) groups, pro-\(p\) groups,
and Golod--Shafarevich criteria. It also develops completed group algebras,
Fox differentials, Reidemeister--Schreier theory, and Crowell exact sequences.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Free pro-\(\mathcal C\) groups](Nyll/ProCGroups/FreeProC/Basic.lean) | The universal property for a free pro-\(\mathcal C\) group on a topological generating space. |
| [Weighted Golod--Shafarevich criterion](Nyll/ProCGroups/GolodShafarevich/WeightedFiniteCriterion.lean) | A nonpositive weighted Golod--Shafarevich polynomial forces the target of a finite pro-\(p\) presentation to be infinite. |
| [Discrete Crowell sequence](Nyll/ProCGroups/CrowellExactSequence/Discrete/MainTheorem.lean) | Exactness of the discrete four-term Crowell sequence for a surjective group homomorphism. |
| [Completed Crowell sequence](Nyll/ProCGroups/CrowellExactSequence/Profinite/MainTheorem.lean) | Exactness of the separated completed Crowell sequence over pro-\(\mathcal C\) integer coefficients under the stated formation and source hypotheses. |

The current library also includes finite and profinite abelian
[Pontryagin biduality](Nyll/ProCGroups/Abelian/ProfiniteBidual.lean), the
[full Tate module](Nyll/ProCGroups/Abelian/FullTateModule.lean) as an inverse
limit of actual torsion subgroups, and
[recognition of the profinite integers](Nyll/ProCGroups/Completion/ProfiniteIntegerRecognition.lean)
from a topological generator and finite quotients of every positive order.

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

Elaboration and linter options are shared in `lakefile.toml`:
`autoImplicit = false`, unused-variable and missing-documentation checks,
and the standard linter set. Maintained sources do not override these options.

## Verification

The [GitHub Actions workflow](.github/workflows/lean.yml) checks that every
maintained source is reachable from `Nyll`, builds with warnings
as errors, audits all declarations for proof placeholders and unexpected axioms,
checks proofs with NanoDa, and replays them with the Lean kernel. It also checks
that the designated declarations in the [public API contract](.github/verification/main-declarations.json)
retain their names, kinds, and specified source modules. This API check does not compare
theorem statements. Logs and receipts are uploaded as workflow artifacts.

CI builds local modules in dependency-depth stages and saves completed project
compiler outputs after each stage. The cache excludes downloaded dependencies,
toolchains, and large generated `*.setup.json` inputs. It checks the available
archive space before saving and validates cached file hashes on restoration;
a missing or invalid cache falls back to a normal build. A separate verification
job still runs the complete declaration, NanoDa, and Lean kernel checks on every
run, including cache hits. Build stages stop after five hours to leave time for
saving completed outputs and diagnostic receipts before the runner deadline.

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and preparation of this repository.
[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) is the human author and responsible maintainer.

## License

Apache License 2.0. See [LICENSE](LICENSE).
