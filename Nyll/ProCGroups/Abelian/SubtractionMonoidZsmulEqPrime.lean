/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith

/-!
# Subtraction Monoid exists zsmul eq of forall prime
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace SubtractionMonoid_exists_zsmul_eq_of_forall_prime


theorem _root_.SubtractionMonoid.exists_zsmul_eq_of_forall_prime {A : Type*} [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, (p : ℤ) • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x := by
  have core : ∀ k : ℕ, k ≠ 0 → ∀ x : A, ∃ y : A, (k : ℤ) • y = x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk x
      rcases eq_or_ne k 1 with rfl | hk1
      · exact ⟨x, one_zsmul x⟩
      · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, k = p * m := by
          obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hk1
          exact ⟨p, hp, hd⟩
        have hm : m ≠ 0 := fun h0 => hk (by rw [h0, mul_zero])
        have hmlt : m < p * m := by nlinarith [hp.one_lt, Nat.pos_of_ne_zero hm]
        obtain ⟨z, hz⟩ := h p hp x
        obtain ⟨y, hy⟩ := ih m hmlt hm z
        exact ⟨y, by rw [Nat.cast_mul, mul_zsmul, hy, hz]⟩
  intro n hn x
  have hna : n.natAbs ≠ 0 := fun h0 => hn (Int.natAbs_eq_zero.mp h0)
  rcases Int.natAbs_eq n with he | he
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨y, by rw [he]; exact hy⟩
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨-y, by rw [he, neg_zsmul, zsmul_neg, neg_neg, hy]⟩

end AlgebraicCurves.Foundations.Algebra.Proofs.SubtractionMonoid_exists_zsmul_eq_of_forall_prime
end ProofImplementation
