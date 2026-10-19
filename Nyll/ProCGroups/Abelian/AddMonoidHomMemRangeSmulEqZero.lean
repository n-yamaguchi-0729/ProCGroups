/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Add Monoid Hom mem range of smul eq zero of nat Card ker mul le of nat Card mul le
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le

theorem _root_.AddMonoidHom.mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
    {T J : Type*} [AddCommGroup T] [AddCommGroup J] (f : T →+ J) (q : ℤ) (hT : ∀ t : T, q • t = 0)
    [Finite T] (hfinJ : Finite {x : J // q • x = 0}) (X Y : ℕ) (hY : 0 < Y)
    (hker : Nat.card f.ker * X ≤ Nat.card T * Y) (hJ : Nat.card {x : J // q • x = 0} * Y ≤ X) :
    ∀ x : J, q • x = 0 → x ∈ f.range := by
  classical
  have := hfinJ
  let ι : f.range → {x : J // q • x = 0} := fun y => ⟨y.1, by
    obtain ⟨t, ht⟩ := y.2
    rw [← ht, ← map_zsmul, hT, map_zero]⟩
  have hι : Function.Injective ι := by
    intro a b h
    have h' : ((ι a : {x : J // q • x = 0}) : J) = ((ι b : {x : J // q • x = 0}) : J) := congrArg
      Subtype.val h
    exact Subtype.ext h'
  have hT' : Nat.card T = Nat.card f.ker * Nat.card f.range := by
    rw [(f.ker).card_eq_card_quotient_mul_card_addSubgroup,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have h1 : X ≤ Nat.card f.range * Y := by
    have h := hker
    rw [hT', mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h hkpos
  have h2 : Nat.card {x : J // q • x = 0} ≤ Nat.card f.range :=
    Nat.le_of_mul_le_mul_right (hJ.trans h1) hY
  have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le h2
  intro x hx
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
  have : (y : J) = x := congrArg Subtype.val hy
  rw [← this]
  exact y.2
end AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
