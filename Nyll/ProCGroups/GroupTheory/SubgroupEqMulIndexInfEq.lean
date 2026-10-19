/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Subgroup_exists_eq_mul_of_index_inf_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group

/-!
# Subgroup exists eq mul of index inf eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Subgroup_exists_eq_mul_of_index_inf_eq

open MulAction

namespace S11Orbit2

variable {G : Type*} [Group G]

theorem stabilizer_mk_one_eq (H₁ H₂ : Subgroup G) :
    stabilizer H₂ ((1 : G) : G ⧸ H₁) = H₁.subgroupOf H₂ := by
  ext h
  have key : h • ((1 : G) : G ⧸ H₁) = (((h : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, key, mul_one, QuotientGroup.eq, mul_one,
    inv_mem_iff]

theorem exists_eq_mul_of_index_inf_eq [Finite G] (H₁ H₂ : Subgroup G)
    (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by
  have hrel : H₁.relIndex H₂ = H₁.index := by
    have h1 : H₁.relIndex H₂ * H₂.index = (H₁ ⊓ H₂).index := by
      rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex_mul_index inf_le_right]
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hcard : (orbit H₂ ((1 : G) : G ⧸ H₁)).ncard = (Set.univ : Set (G ⧸ H₁)).ncard := by
    rw [← index_stabilizer, stabilizer_mk_one_eq, Set.ncard_univ, ← Subgroup.index_eq_card]
    exact hrel
  have huniv : orbit H₂ ((1 : G) : G ⧸ H₁) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hcard.ge Set.finite_univ
  have hmem : ((g⁻¹ : G) : G ⧸ H₁) ∈ orbit H₂ ((1 : G) : G ⧸ H₁) := huniv ▸ Set.mem_univ _
  obtain ⟨h₂, hh₂⟩ := mem_orbit_iff.mp hmem
  have key : h₂ • ((1 : G) : G ⧸ H₁) = (((h₂ : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [key, mul_one, QuotientGroup.eq] at hh₂
  refine ⟨g * h₂, ?_, (h₂ : G)⁻¹, H₂.inv_mem h₂.2, by group⟩
  have := H₁.inv_mem hh₂
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

end S11Orbit2

theorem _root_.Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G] (H₁ H₂ :
  Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ :=
  S11Orbit2.exists_eq_mul_of_index_inf_eq H₁ H₂ h g
end AlgebraicCurves.Foundations.Algebra.Proofs.Subgroup_exists_eq_mul_of_index_inf_eq
end ProofImplementation
