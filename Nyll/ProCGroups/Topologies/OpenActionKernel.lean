/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Open kernels of compact-group actions on finite quotients

For a continuous action preserving an open subgroup of a compact commutative
group, its finite quotient has an open action kernel. No topology on an
automorphism group is required.
-/

namespace ProCGroups

/-- A continuous action is trivial modulo an invariant open subgroup after
restriction to an open subgroup of the acting group. -/
theorem exists_open_subgroup_action_trivial_mod
    {Γ B : Type*} [Group Γ] [TopologicalSpace Γ]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B]
    (N : Subgroup B) (hN : IsOpen (N : Set B))
    (ρ : Γ →* MulAut B)
    (hpres : ∀ σ b, b ∈ N → ρ σ b ∈ N)
    (hρ : ∀ b : B, Continuous (fun σ : Γ => ρ σ b)) :
    ∃ U : OpenSubgroup Γ, ∀ σ ∈ U, ∀ b : B, ρ σ b / b ∈ N := by
  classical
  let : MulAction Γ B := MulAction.compHom B ρ
  let : MulAction.QuotientAction Γ N :=
    { inv_mul_mem := by
        intro σ a a' h
        change (ρ σ a)⁻¹ * ρ σ a' ∈ N
        simpa only [map_mul, map_inv] using hpres σ (a⁻¹ * a') h }
  let Q := B ⧸ N
  let : Finite Q := N.quotient_finite_of_isOpen hN
  let K : Subgroup Γ := (MulAction.toPermHom Γ Q).ker
  have hfix (σ : Γ) : σ ∈ K ↔ ∀ q : Q, σ • q = q := by
    change (MulAction.toPermHom Γ Q σ = 1) ↔ _
    exact Equiv.Perm.ext_iff
  have hfix_rep (σ : Γ) (q : Q) :
      σ • q = q ↔ ρ σ q.out / q.out ∈ N := by
    have h :
        (σ • (QuotientGroup.mk q.out : Q) = (QuotientGroup.mk q.out : Q)) ↔
          ρ σ q.out / q.out ∈ N := by
      change (QuotientGroup.mk (ρ σ q.out) : Q) = QuotientGroup.mk q.out ↔ _
      exact QuotientGroup.eq_iff_div_mem
    simpa only [QuotientGroup.out_eq'] using h
  have hKset : (K : Set Γ) =
      ⋂ q : Q, (fun σ : Γ => ρ σ q.out / q.out) ⁻¹' (N : Set B) := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact (hfix σ).trans (forall_congr' (hfix_rep σ))
  have hKopen : IsOpen (K : Set Γ) := by
    rw [hKset]
    exact isOpen_iInter_of_finite fun q =>
      hN.preimage ((hρ q.out).div' continuous_const)
  refine ⟨⟨K, hKopen⟩, ?_⟩
  intro σ hσ b
  have h := (hfix σ).mp hσ (QuotientGroup.mk b)
  change (QuotientGroup.mk (ρ σ b) : Q) = QuotientGroup.mk b at h
  exact QuotientGroup.eq_iff_div_mem.mp h

/-- In particular, an open power subgroup is automatically invariant. -/
theorem exists_open_subgroup_action_trivial_mod_powers
    {Γ B : Type*} [Group Γ] [TopologicalSpace Γ]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B]
    (n : ℕ) (hn : IsOpen {b : B | ∃ c : B, c ^ n = b})
    (ρ : Γ →* MulAut B)
    (hρ : ∀ b : B, Continuous (fun σ : Γ => ρ σ b)) :
    ∃ U : OpenSubgroup Γ, ∀ σ ∈ U, ∀ b : B, ∃ c : B, c ^ n = ρ σ b / b := by
  let N : Subgroup B := (powMonoidHom n : B →* B).range
  have hN : IsOpen (N : Set B) := hn
  have hpres (σ : Γ) (b : B) (hb : b ∈ N) : ρ σ b ∈ N := by
    obtain ⟨c, hc⟩ := hb
    refine ⟨ρ σ c, ?_⟩
    change c ^ n = b at hc
    change (ρ σ c) ^ n = ρ σ b
    rw [← map_pow, hc]
  exact exists_open_subgroup_action_trivial_mod N hN ρ hpres hρ

end ProCGroups
