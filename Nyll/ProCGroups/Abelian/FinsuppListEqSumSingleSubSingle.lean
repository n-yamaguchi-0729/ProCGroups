/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Tauto

/-!
# Finsupp exists list eq sum single sub single of sum fibre eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero

namespace Finsupp
open _root_.Finsupp

variable {α β : Type*} [DecidableEq β] (ℓ : α → β)

private theorem sum_filter_eq_of_support_subset (D : α →₀ ℤ) (T : Finset α) (hT : D.support ⊆ T) (b
  : β) :
    ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = (T.filter fun a => ℓ a = b).sum fun a
      => D a := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hT)
  intro a _ ha
  rw [Finset.mem_filter, not_and'] at ha
  by_contra h0
  exact ha (by rw [Finset.mem_filter] at *; tauto) (Finsupp.mem_support_iff.mpr h0)

private theorem exists_pos_neg_of_sum_fibre_eq_zero (D : α →₀ ℤ)
    (hD : ∀ b : β, ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = 0) (hD0 : D ≠ 0) :
    ∃ x y : α, ℓ x = ℓ y ∧ 0 < D x ∧ D y < 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a ∈ D.support := by
    by_contra h
    push Not at h
    exact hD0 (Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem h))
  have ha0 : D a ≠ 0 := Finsupp.mem_support_iff.mp ha
  set Fb := D.support.filter fun c => ℓ c = ℓ a with hFb
  have haF : a ∈ Fb := Finset.mem_filter.mpr ⟨ha, rfl⟩
  have hsum : (Fb.sum fun c => D c) = 0 := hD (ℓ a)
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  · have : ∃ x ∈ Fb, 0 < D x := by
      by_contra h
      push Not at h
      have hle : (Fb.sum fun c => D c) ≤ D a := by
        rw [← Finset.sum_erase_add _ _ haF]
        have : ((Fb.erase a).sum fun c => D c) ≤ 0 := Finset.sum_nonpos fun c hc => h c
          (Finset.mem_of_mem_erase hc)
        linarith
      linarith
    obtain ⟨x, hx, hxpos⟩ := this
    exact ⟨x, a, (Finset.mem_filter.mp hx).2, hxpos, hneg⟩
  · have : ∃ y ∈ Fb, D y < 0 := by
      by_contra h
      push Not at h
      have hle : D a ≤ (Fb.sum fun c => D c) := by
        rw [← Finset.sum_erase_add _ _ haF]
        have : 0 ≤ ((Fb.erase a).sum fun c => D c) := Finset.sum_nonneg fun c hc => h c
          (Finset.mem_of_mem_erase hc)
        linarith
      linarith
    obtain ⟨y, hy, hyneg⟩ := this
    exact ⟨a, y, ((Finset.mem_filter.mp hy).2).symm, hpos, hyneg⟩

end Finsupp

theorem _root_.Finsupp.exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
    {α β : Type*} [DecidableEq β] (ℓ : α → β) (D : α →₀ ℤ)
    (hD : ∀ b : β, ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = 0) :
    ∃ l : List (α × α), (∀ p ∈ l, ℓ p.1 = ℓ p.2 ∧ p.1 ∈ D.support ∧ p.2 ∈ D.support ∧ p.1 ≠ p.2) ∧
      D = (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : α →₀ ℤ)).sum := by
  classical
  suffices H : ∀ (N : ℕ) (D : α →₀ ℤ), (D.support.sum fun a => (D a).natAbs) = N →
      (∀ b : β, ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = 0) →
      ∃ l : List (α × α), (∀ p ∈ l, ℓ p.1 = ℓ p.2 ∧ p.1 ∈ D.support ∧ p.2 ∈ D.support ∧ p.1 ≠ p.2) ∧
        D = (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : α →₀ ℤ)).sum from
    H _ D rfl hD
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro D hN hD
    by_cases hD0 : D = 0
    · exact ⟨[], fun _ hp => (List.not_mem_nil hp).elim, hD0⟩
    obtain ⟨x, y, hxy, hx, hy⟩ := Finsupp.exists_pos_neg_of_sum_fibre_eq_zero ℓ D hD hD0
    have hxs : x ∈ D.support := Finsupp.mem_support_iff.mpr hx.ne'
    have hys : y ∈ D.support := Finsupp.mem_support_iff.mpr hy.ne
    have hxy' : x ≠ y := by rintro rfl; linarith
    set D' : α →₀ ℤ := D - (Finsupp.single x 1 - Finsupp.single y 1) with hD'
    have hD'app : ∀ a, D' a = D a - (if x = a then 1 else 0) + (if y = a then 1 else 0) := by
      intro a; simp only [hD', Finsupp.sub_apply, Finsupp.single_apply]; ring
    have hsupp : D'.support ⊆ D.support := by
      intro a ha
      rw [Finsupp.mem_support_iff] at ha ⊢
      intro h0
      apply ha
      rw [hD'app, h0]
      have hxa : x ≠ a := fun h => by rw [← h] at h0; exact hx.ne' h0
      have hya : y ≠ a := fun h => by rw [← h] at h0; exact hy.ne h0
      rw [ite_eq_right hxa, ite_eq_right hya]; ring
    have hD'fib : ∀ b : β, ((D'.support.filter fun a => ℓ a = b).sum fun a => D' a) = 0 := by
      intro b
      rw [Finsupp.sum_filter_eq_of_support_subset ℓ D' D.support hsupp b]
      have h1 : ((D.support.filter fun a => ℓ a = b).sum fun a => D' a) =
          ((D.support.filter fun a => ℓ a = b).sum fun a => D a) -
          ((D.support.filter fun a => ℓ a = b).sum fun a => (if x = a then (1 : ℤ) else 0)) +
          ((D.support.filter fun a => ℓ a = b).sum fun a => (if y = a then (1 : ℤ) else 0)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => hD'app a
      rw [h1, hD b, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp only [Finset.mem_filter, hxs, hys, true_and]
      by_cases hb : ℓ x = b
      · rw [ite_eq_left hb, ite_eq_left (hxy ▸ hb)]; ring
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb (hxy ▸ h))]; ring
    have hmass : (D'.support.sum fun a => (D' a).natAbs) + 2 = N := by
      have hT : (D'.support.sum fun a => (D' a).natAbs) = D.support.sum fun a => (D' a).natAbs := by
        apply Finset.sum_subset hsupp
        intro a _ ha
        rw [Finsupp.notMem_support_iff.mp ha, Int.natAbs_zero]
      rw [hT, ← hN, ← Finset.sum_erase_add _ _ hxs, ← Finset.sum_erase_add _ _ hxs,
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hxy', hys⟩),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hxy', hys⟩)]
      have hrest : (((D.support.erase x).erase y).sum fun a => (D' a).natAbs) =
          ((D.support.erase x).erase y).sum fun a => (D a).natAbs := by
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨hay, hax⟩ : a ≠ y ∧ a ∈ D.support.erase x := Finset.mem_erase.mp ha
        have hax' : a ≠ x := (Finset.mem_erase.mp hax).1
        rw [hD'app, ite_eq_right (Ne.symm hax'), ite_eq_right (Ne.symm hay)]; ring_nf
      have hxv : (D' x).natAbs + 1 = (D x).natAbs := by
        rw [hD'app, ite_eq_left rfl, ite_eq_right (Ne.symm hxy')]
        omega
      have hyv : (D' y).natAbs + 1 = (D y).natAbs := by
        rw [hD'app, ite_eq_right hxy', ite_eq_left rfl]
        omega
      rw [hrest]; omega
    obtain ⟨l, hl, hlsum⟩ := ih _ (by omega) D' rfl hD'fib
    refine ⟨(x, y) :: l, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hxy, hxs, hys, hxy'⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hl p hp
        exact ⟨h1, hsupp h2, hsupp h3, h4⟩
    · rw [List.map_cons, List.sum_cons, ← hlsum, hD']
      abel
end Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
