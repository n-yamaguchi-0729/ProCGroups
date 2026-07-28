# ProCGroups

This repository is the standalone Lean 4 source project for `ProCGroups`, a
library for profinite groups and pro-\(\mathcal C\) groups. Local class field
theory is maintained separately.

Documentation and the library catalog are published through the
[Yamaguchi Lean 4 Library](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/).

## Contents

- 574 Lean source files, including the public root module
  `Lean4/ProCGroups.lean`.
- Foundations for profinite groups, pro-\(\mathcal C\) groups, free
  constructions, completed group algebras, Fox differentials, and related
  topics.
- The Crowell exact sequence implementation is collected under
  `ProCGroups.CrowellExactSequence`. Its main aggregate is
  `Lean4/ProCGroups/CrowellExactSequence.lean`.

The project uses Lean 4.32.1 and mathlib v4.32.1.

## Build

From the repository root:

```console
lake update
lake exe cache get
lake --wfail build ProCGroups
```

## Import

Import the whole public library:

```lean
import ProCGroups
```

Or import a narrower aggregate, for example:

```lean
import ProCGroups.CrowellExactSequence
```

This library was developed with AI assistance by a non-specialist; please review the material independently.

## License

Apache License 2.0. See [LICENSE](LICENSE).
