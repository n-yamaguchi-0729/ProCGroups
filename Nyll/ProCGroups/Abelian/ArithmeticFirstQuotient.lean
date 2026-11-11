/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.ProCGroups.Topologies.Conjugation
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# The arithmetic first abelian quotient

The first quotient kills the closed commutator of the geometric subgroup.
Its canonical projection and the geometric preimages of first-layer covers
are defined independently of any mixed quotient.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

universe u v

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- The full geometric closed commutator embedded in the arithmetic group. -/
def arithmeticFirstKernel (D : Subgroup P) : Subgroup P :=
  (Subgroup.closedCommutator D).map D.subtype

variable (D : Subgroup P) [D.Normal]

instance arithmeticFirstKernel_normal : (arithmeticFirstKernel D).Normal := by
  refine ⟨?_⟩
  rintro x ⟨d, hd, rfl⟩ g
  let c : D →ₜ* D :=
    ContinuousMonoidHom.toContinuousMonoidHom (Subgroup.conjNormalContinuousMulEquiv D g)
  exact ⟨c d, Subgroup.closedCommutator_map_le c ⟨d, hd, rfl⟩, rfl⟩

/-- The arithmetic quotient with the entire first geometric abelian layer. -/
abbrev ArithmeticFirstQuotient := P ⧸ arithmeticFirstKernel D

/-- The actual arithmetic projection to the first geometric abelian quotient. -/
def arithmeticFirstMk : P →ₜ* ArithmeticFirstQuotient D :=
  { toMonoidHom := QuotientGroup.mk' (arithmeticFirstKernel D)
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The original arithmetic map descends while retaining the full first geometric layer. -/
def arithmeticFirstProjection
    {Γ : Type v} [Group Γ] [TopologicalSpace Γ] (π : P →ₜ* Γ) :
    ArithmeticFirstQuotient π.toMonoidHom.ker →ₜ* Γ :=
  QuotientGroup.liftₜ (arithmeticFirstKernel π.toMonoidHom.ker) π (by
    rintro x ⟨d, _, rfl⟩
    exact d.property)

/-- The marked first-layer projection is the original arithmetic map on representatives. -/
@[simp] theorem arithmeticFirstProjection_apply_mk
    {Γ : Type v} [Group Γ] [TopologicalSpace Γ] (π : P →ₜ* Γ) (g : P) :
    arithmeticFirstProjection π (arithmeticFirstMk π.toMonoidHom.ker g) = π g := rfl

/-- The geometric subgroup of the actual arithmetic preimage of a first-layer cover. -/
def firstCoverGeometricSubgroup (H : OpenSubgroup (ArithmeticFirstQuotient D)) : Subgroup D :=
  (H.toSubgroup.comap (arithmeticFirstMk D).toMonoidHom).subgroupOf D

/-- Every first-layer arithmetic cover has abelian geometric deck group: its
geometric preimage contains the original closed commutator. -/
theorem closedCommutator_le_firstCoverGeometricSubgroup
    (H : OpenSubgroup (ArithmeticFirstQuotient D)) :
    Subgroup.closedCommutator D ≤ firstCoverGeometricSubgroup D H := by
  intro d hd
  change arithmeticFirstMk D (d : P) ∈ H
  have hmk : arithmeticFirstMk D (d : P) = 1 :=
    (QuotientGroup.eq_one_iff (N := arithmeticFirstKernel D) (d : P)).mpr ⟨d, hd, rfl⟩
  rw [hmk]
  exact H.one_mem


end ProCGroups.Abelian
