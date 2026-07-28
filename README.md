# ProCGroups v2

`ProCGroups` is a standalone Lean 4 library for profinite groups and pro-\(\mathcal C\)
groups. Version 2 separates this library from the former monolithic
`YamaLean4Lib` project; local class field theory is not part of this repository.

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

## Disclaimer

作者はこの分野の専門家ではありません。本ライブラリの作成には AI
アシスタントを使用しています。内容の正確性・完全性は保証されないため、利用者自身で
検証し、自己責任で使用してください。作者は数学的内容、Lean コード、利用方法に関する
質問への回答や個別サポートを提供できません。

The author is not a subject-matter expert and used AI assistants while developing
this library. No guarantee is made about correctness or completeness. Verify
the material independently and use it at your own risk. The author cannot
answer questions or provide individual support.

## License

Apache License 2.0. See [LICENSE](LICENSE).
