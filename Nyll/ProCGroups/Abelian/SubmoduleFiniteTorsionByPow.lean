/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Submodule finite torsion By pow of finite torsion By
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Submodule_finite_torsionBy_pow_of_finite_torsionBy

theorem _root_.Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by
  have hS : {x : M | a • x = 0}.Finite := by
    have : {x : M | a • x = 0} = (Submodule.torsionBy R M a : Set M) := by
      ext x
      exact (Submodule.mem_torsionBy_iff a x).symm
    rw [this]
    exact Set.toFinite _
  suffices H : ∀ k : ℕ, {x : M | a ^ k • x = 0}.Finite by
    have hk := H k
    have : {x : M | a ^ k • x = 0} = (Submodule.torsionBy R M (a ^ k) : Set M) := by
      ext x
      exact (Submodule.mem_torsionBy_iff (a ^ k) x).symm
    rw [this] at hk
    exact hk.to_subtype
  intro k
  induction k with
  | zero =>
      refine (Set.finite_singleton (0 : M)).subset ?_
      intro x hx
      change a ^ 0 • x = 0 at hx
      rw [pow_zero, one_smul] at hx
      exact hx
  | succ k ih =>
      have hfib : ∀ y : M, {x : M | a ^ k • x = y}.Finite := by
        intro y
        rcases Set.eq_empty_or_nonempty {x : M | a ^ k • x = y} with he | ⟨x₀, hx₀⟩
        · rw [he]; exact Set.finite_empty
        · refine (ih.image fun s => x₀ + s).subset ?_
          intro x hx
          simp only [Set.mem_ofPred_eq] at hx hx₀
          refine ⟨x - x₀, ?_, (add_comm x₀ (x - x₀)).trans (sub_add_cancel x x₀)⟩
          simp only [Set.mem_ofPred_eq, smul_sub, hx, hx₀, sub_self]
      refine (hS.biUnion fun y _ => hfib y).subset ?_
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      refine Set.mem_biUnion (x := a ^ k • x) ?_ rfl
      simp only [Set.mem_ofPred_eq, smul_smul, ← pow_succ', hx]
end AlgebraicCurves.Foundations.Algebra.Proofs.Submodule_finite_torsionBy_pow_of_finite_torsionBy
end ProofImplementation
