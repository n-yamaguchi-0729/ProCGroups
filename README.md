# ProCGroups (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ProCGroups/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4.35.0-rc2 library for profinite groups and pro-\(\mathcal C\) groups. It covers
finite quotients, completions, free pro-\(\mathcal C\) groups, pro-\(p\) groups,
and Golod--Shafarevich criteria. It also develops completed group algebras,
Fox differentials, Reidemeister--Schreier theory, and Crowell exact sequences.
Its only Lake dependency is [Mathlib](https://github.com/leanprover-community/mathlib4).

## Public API

Import the complete library with:

```lean
import ProCGroups.All
```

Focused aggregates let you import the part you need, for example:

```lean
import ProCGroups.FreeProC.All
import ProCGroups.ProP.All
import ProCGroups.GolodShafarevich.All
import ProCGroups.CrowellExactSequence.All
```

Other focused aggregates cover finite groups, inverse systems, completions,
pro-\(\mathcal C\) groups, free products, completed group algebras, and Fox
differentials. Individual result files can also be imported directly; the
linked files below are examples.

## Main results

| Declaration | Mathematical content |
| --- | --- |
| [`ProCGroups.FreeProC.IsFreeProCGroup`](Lean4/ProCGroups/FreeProC/Basic.lean) | The universal property for a free pro-\(\mathcal C\) group on a topological generating space. |
| [`ClassFieldTower.ProP.FiniteProPPresentation.infinite_of_gsPolynomial_nonpos`](Lean4/ProCGroups/GolodShafarevich/WeightedFiniteCriterion.lean) | A nonpositive weighted Golod--Shafarevich polynomial forces the target of a finite pro-\(p\) presentation to be infinite. |
| [`CrowellExactSequence.discreteCrowellLinearSequence_isExact`](Lean4/ProCGroups/CrowellExactSequence/Discrete/MainTheorem.lean) | Exactness of the discrete four-term Crowell sequence for a surjective group homomorphism. |
| [`CrowellExactSequence.profiniteSeparatedCrowellLinearSequence_isExact`](Lean4/ProCGroups/CrowellExactSequence/Profinite/MainTheorem.lean) | Exactness of the separated completed Crowell sequence over pro-\(\mathcal C\) integer coefficients under the stated formation and source hypotheses. |

The current library also includes finite and profinite abelian
[Pontryagin biduality](Lean4/ProCGroups/Abelian/ProfiniteBidual.lean), the
[full Tate module](Lean4/ProCGroups/Abelian/FullTateModule.lean) as an inverse
limit of actual torsion subgroups, and
[recognition of the profinite integers](Lean4/ProCGroups/Completion/ProfiniteIntegerRecognition.lean)
from a topological generator and finite quotients of every positive order.
### Scope of the Tate-module construction

`FullTateModule M` is defined for an arbitrary additive commutative group
`M`: it is the inverse limit of the subgroups `M[n]`, with multiplication
as transition maps. This is a group-theoretic construction, not a definition
of an étale fundamental group. It does not take a scheme, curve, or geometric
point as input, and it does not depend on SchemeTheory or
EtaleFundamentalGroups.

The actual finite étale covers, geometric fibre functors, and étale
fundamental groups belong to
[EtaleFundamentalGroups](https://github.com/n-yamaguchi-0729/lean4-math-library/tree/main/Lean4/EtaleFundamentalGroups)
in the development workspace. The geometric comparison for an abelian
variety is implemented there in
[AbelianTateComparison.lean](https://github.com/n-yamaguchi-0729/lean4-math-library/blob/main/Lean4/EtaleFundamentalGroups/GeometricFiber/AbelianTateComparison.lean);
it applies the abstract Tate-module construction to actual algebraic points.
That comparison is not a theorem of this standalone ProCGroups package.
The general curve's actual Abel–Jacobi-induced Tate comparison remains
separate work and is not claimed here.

## Build

The repository pins Lean 4.35.0-rc2 and an exact Mathlib revision in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).
The dependency lock is in [`lake-manifest.json`](lake-manifest.json).
From the repository root:

```console
lake exe cache get
lake --wfail build
```

Elaboration and linter options are shared in `lakefile.toml`:
`autoImplicit = false`, unused-variable and missing-documentation checks,
and the Mathlib standard linter set. Maintained sources do not override these options.

## Verification

The [GitHub Actions workflow](.github/workflows/lean.yml) checks that every
maintained source is reachable from `ProCGroups.All`, builds with warnings
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
