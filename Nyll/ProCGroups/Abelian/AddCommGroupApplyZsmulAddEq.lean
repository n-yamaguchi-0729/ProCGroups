/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF

/-!
# Add Comm Group apply zsmul add eq of forall cube
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.AddCommGroup_apply_zsmul_add_eq_of_forall_cube

namespace P2mQuad

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem tri_succ (n : ℤ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h : (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_zero : (0 : ℤ) * (0 - 1) / 2 = 0 := by norm_num

theorem eq_of_second_difference (g : ℤ → N) (D : N)
    (h : ∀ n : ℤ, g (n + 2) - 2 • g (n + 1) + g n = D) (n : ℤ) :
    g n = g 0 + n • (g 1 - g 0) + (n * (n - 1) / 2) • D := by
  have h1 : ∀ n : ℤ, g (n + 1) - g n = (g 1 - g 0) + n • D := by
    intro n
    induction n using Int.induction_on with
    | zero => simp only [zero_add, zero_smul, add_zero]
    | succ k ih =>
      have hk := h k
      have e : (k : ℤ) + 1 + 1 = k + 2 := by ring
      rw [e]
      have : g (k + 2) - g (k + 1) = (g (k + 1) - g k) + D := by
        rw [← hk]; abel
      rw [this, ih, add_smul, one_smul]
      abel
    | pred k ih =>
      have hk := h (-(k : ℤ) - 1)
      have e1 : (-(k : ℤ) - 1 + 2) = -k + 1 := by ring
      have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
      rw [e1, e2] at hk
      rw [e2]
      have : g (-(k : ℤ)) - g (-k - 1) = (g (-k + 1) - g (-k)) - D := by
        rw [← hk]; abel
      rw [this, ih, sub_smul, one_smul]
      abel
  induction n using Int.induction_on with
  | zero => simp only [tri_zero, zero_smul, add_zero]
  | succ k ih =>
    have := h1 k
    rw [tri_succ, add_smul, eq_add_of_sub_eq' this |>.trans (by rfl), ih, add_smul, one_smul]
    abel
  | pred k ih =>
    have hk := h1 (-(k : ℤ) - 1)
    have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
    rw [e2] at hk
    have : g (-(k : ℤ) - 1) = g (-k) - ((g 1 - g 0) + (-(k : ℤ) - 1) • D) := by
      rw [← hk]; abel
    rw [this, ih]
    have ht : (-(k : ℤ)) * (-(k : ℤ) - 1) / 2 = (-(k : ℤ) - 1) * (-(k : ℤ) - 1 - 1) / 2 + (-(k : ℤ)
      - 1) := by
      have := tri_succ (-(k : ℤ) - 1)
      rw [e2] at this
      exact this
    rw [ht, add_smul, sub_smul, sub_smul, one_smul]
    abel

theorem main (Λ : M → N)
    (hΛ : ∀ x y z : M, Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) = Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0)
      := by
  set g : ℤ → M := fun n => n • x + y with hg
  have h2 : ∀ n : ℤ, Λ (g (n + 2)) - 2 • Λ (g (n + 1)) + Λ (g n) = Λ (2 • x) - 2 • Λ x + Λ 0 := by
    intro n
    have hc := hΛ (n • x + y) x x
    have e1 : n • x + y + x + x = g (n + 2) := by simp only [hg]; module
    have e2 : n • x + y + x = g (n + 1) := by simp only [hg]; module
    have e3 : x + x = 2 • x := (two_nsmul x).symm
    rw [e1, e2, e3] at hc
    have e4 : Λ (g n) = Λ (n • x + y) := rfl
    rw [two_nsmul (Λ (g (n + 1))), two_nsmul (Λ x)]
    have := hc
    calc Λ (g (n + 2)) - (Λ (g (n + 1)) + Λ (g (n + 1))) + Λ (g n)
        = (Λ (g (n + 2)) - Λ (g (n + 1)) - Λ (g (n + 1)) - Λ (2 • x) + Λ (n • x + y) + Λ x + Λ x)
            + (Λ (2 • x) - (Λ x + Λ x)) := by rw [e4]; abel
      _ = Λ 0 + (Λ (2 • x) - (Λ x + Λ x)) := by rw [this]
      _ = Λ (2 • x) - (Λ x + Λ x) + Λ 0 := by abel
  have hmain := eq_of_second_difference (fun n => Λ (g n)) _ h2 n
  have g0 : g 0 = y := by simp only [hg, zero_smul, zero_add]
  have g1 : g 1 = x + y := by simp only [hg, one_smul]
  simp only [g0, g1] at hmain
  exact hmain

end P2mQuad

theorem _root_.AddCommGroup.apply_zsmul_add_eq_of_forall_cube
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) :=
  P2mQuad.main Λ hΛ x y n
end AlgebraicCurves.Foundations.Algebra.Proofs.AddCommGroup_apply_zsmul_add_eq_of_forall_cube
end ProofImplementation
