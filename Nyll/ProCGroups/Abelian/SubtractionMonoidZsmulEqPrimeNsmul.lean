/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.ProCGroups.Abelian.SubtractionMonoidZsmulEqPrime

/-!
# Subtraction Monoid exists zsmul eq of forall prime nsmul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul


theorem _root_.SubtractionMonoid.exists_zsmul_eq_of_forall_prime_nsmul {A : Type*}
  [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, p • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x :=
  SubtractionMonoid.exists_zsmul_eq_of_forall_prime (fun p hp x =>
    (h p hp x).imp fun y hy => by rw [natCast_zsmul]; exact hy)

end SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
