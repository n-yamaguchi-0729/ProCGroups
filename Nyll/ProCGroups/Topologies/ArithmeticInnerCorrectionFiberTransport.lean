/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Explicit inner correction of a group map and its same fibre map

An arithmetic discrepancy can be removed by an actual lift in the target
covering group. The resulting fibre equivalence is explicitly translated by
that same lift. Thus neither the group map nor its selected fibre point is
silently treated as unchanged.
-/
noncomputable section

namespace ProCGroups

/-- Conjugation by the specified element of the actual topological group. -/
def specifiedInnerContinuousMulEquiv
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (c : H) : H ≃ₜ* H where
  toMulEquiv := MulAut.conj c
  continuous_toFun := IsTopologicalGroup.continuous_conj c
  continuous_invFun := by
    change Continuous (fun h : H => c⁻¹ * h * c)
    simpa only [inv_inv] using IsTopologicalGroup.continuous_conj c⁻¹

/-- The exact group-map change made by the target correction. -/
def innerCorrectedGroupEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (α : G ≃ₜ* H) (c : H) : G ≃ₜ* H :=
  α.trans (specifiedInnerContinuousMulEquiv c)

@[simp] theorem innerCorrectedGroupEquiv_apply
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (α : G ≃ₜ* H) (c : H) (g : G) :
    innerCorrectedGroupEquiv α c g = c * α g * c⁻¹ := rfl

/-- Translate the same fibre map by the same actual target-group element. -/
def innerCorrectedFiberEquiv
    {H X Y : Type*} [Group H] [MulAction H Y]
    (e : X ≃ Y) (c : H) : X ≃ Y :=
  e.trans (MulAction.toPerm c)

@[simp] theorem innerCorrectedFiberEquiv_apply
    {H X Y : Type*} [Group H] [MulAction H Y]
    (e : X ≃ Y) (c : H) (x : X) :
    innerCorrectedFiberEquiv e c x = c • e x := rfl

/-- Equivariance is retained by the explicitly changed pair. In particular,
the chosen target point changes from e x to c • e x by this formula. -/
theorem innerCorrectedFiberEquiv_smul
    {G H X Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    [MulAction G X] [MulAction H Y]
    (α : G ≃ₜ* H) (e : X ≃ Y) (he : ∀ g x, e (g • x) = α g • e x)
    (c : H) (g : G) (x : X) :
    innerCorrectedFiberEquiv e c (g • x) =
      innerCorrectedGroupEquiv α c g • innerCorrectedFiberEquiv e c x := by
  change c • e (g • x) = (c * α g * c⁻¹) • (c • e x)
  rw [he]
  simp only [mul_smul, inv_smul_smul]

/-- Surjectivity supplies the correction inside the actual target group.
The same correction has both the exact quotient value and strict arithmetic
compatibility; it is not an independent correction of the fibre data. -/
theorem exists_innerCorrection_strict_quotient
    {G H Γ : Type*} [Group G] [Group H] [Group Γ]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (α : G ≃ₜ* H) (qs : G →* Γ) (qt : H →* Γ)
    (hqt : Function.Surjective qt) (d : Γ)
    (hα : ∀ g, qt (α g) = d * qs g * d⁻¹) :
    ∃ c : H, qt c = d⁻¹ ∧ ∀ g, qt (innerCorrectedGroupEquiv α c g) = qs g := by
  obtain ⟨c, hc⟩ := hqt d⁻¹
  refine ⟨c, hc, fun g => ?_⟩
  rw [innerCorrectedGroupEquiv_apply, map_mul, map_mul, map_inv, hc, hα]
  simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end ProCGroups
