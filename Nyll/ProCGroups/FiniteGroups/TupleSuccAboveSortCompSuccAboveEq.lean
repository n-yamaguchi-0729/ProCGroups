/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Tuple_succAbove_sort_comp_succAbove_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tuple succ Above sort comp succ Above eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Tuple_succAbove_sort_comp_succAbove_eq

theorem _root_.Tuple.succAbove_sort_comp_succAbove_eq
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin
      (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove
      k) := by
  classical
  set s : Equiv.Perm (Fin (n + 1)) := Tuple.sort u with hs
  set p : Fin (n + 1) := s.symm i with hp
  have hsp : s p = i := s.apply_symm_apply i
  let e : {x : Fin (n + 1) // x ≠ p} ≃ {x : Fin (n + 1) // x ≠ i} :=
    s.subtypeEquiv (fun x => by rw [← hsp]; exact s.injective.ne_iff.symm)
  let τ : Equiv.Perm (Fin n) := ((finSuccAboveEquiv p).trans e).trans (finSuccAboveEquiv i).symm
  have hτ : ∀ k : Fin n, i.succAbove (τ k) = s (p.succAbove k) := by
    intro k
    have h1 : finSuccAboveEquiv i (τ k) = e (finSuccAboveEquiv p k) :=
      (finSuccAboveEquiv i).apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    rw [finSuccAboveEquiv_apply] at h2
    simpa [e, Equiv.subtypeEquiv, finSuccAboveEquiv_apply] using h2
  have key : τ = Tuple.sort (u ∘ i.succAbove) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨?_, ?_⟩
    · intro a b hab
      change u (i.succAbove (τ a)) ≤ u (i.succAbove (τ b))
      rw [hτ, hτ]
      exact Tuple.monotone_sort u ((Fin.strictMono_succAbove p).monotone hab)
    · intro a b hab h
      exfalso
      have h' : i.succAbove (τ a) = i.succAbove (τ b) := hu h
      rw [hτ, hτ, s.apply_eq_iff_eq] at h'
      exact absurd (Fin.succAbove_right_injective h') hab.ne
  rw [← key, hτ]
end AlgebraicCurves.Foundations.Algebra.Proofs.Tuple_succAbove_sort_comp_succAbove_eq
end ProofImplementation
