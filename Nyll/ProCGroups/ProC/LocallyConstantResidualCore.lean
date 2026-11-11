/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Residual cores detected by original finite maps and images

A locally constant finite homomorphism kills the relevant residual core
without requiring a topology on its target. Its original source quotient
has the canonical quotient topology and is discrete because the kernel is
open. The same residual core, mapped through a continuous homomorphism of
profinite groups, depends only on that homomorphism's original image.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}

/-- An original locally constant map to a finite group in the class kills
the residual core. Only the source and its canonical quotient need topology. -/
theorem proCResidualCore_le_ker_of_locallyConstant_finite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type u} [Group H]
    (hC : FiniteGroupClass.FullFormation C)
    (f : G →* H) (hf : IsLocallyConstant f) (hH : C H) :
    proCResidualCore C G ≤ f.ker := by
  let e : G ⧸ f.ker ≃* f.range := QuotientGroup.quotientKerEquivRange f
  have hrange : C f.range := hC.hereditary.subgroupClosed f.range hH
  have hquotient : C (G ⧸ f.ker) :=
    hC.melnikovFormation.formation.isomClosed ⟨e.symm⟩ hrange
  have : Finite (G ⧸ f.ker) := C.finite hquotient
  have hopen : IsOpen (f.ker : Set G) := hf.isOpen_fiber 1
  have hclosed : IsClosed (f.ker : Set G) := hf.isClosed_fiber 1
  have : DiscreteTopology (G ⧸ f.ker) := QuotientGroup.discreteTopology hopen
  exact proCResidualCore_le_of_proCQuotient f.ker hclosed
    (HasOpenNormalBasisInClass.of_finite_discrete
      hC.melnikovFormation.formation.quotientClosed hquotient)

section Images

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- The image of the original residual core is the residual core of the
original image, included through its literal subgroup inclusion. -/
theorem map_proCResidualCore_eq_rangeCore
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H) :
    (proCResidualCore C G).map f.toMonoidHom =
      (proCResidualCore C f.toMonoidHom.range).map f.toMonoidHom.range.subtype := by
  let f' : G →ₜ* f.toMonoidHom.range := ContinuousMonoidHom.rangeRestrict f
  have hrange : (proCResidualCore C G).map f'.toMonoidHom =
      proCResidualCore C f.toMonoidHom.range :=
    map_proCResidualCore_eq_of_surjective hC f'.toMonoidHom
      f'.continuous_toFun f.toMonoidHom.rangeRestrict_surjective
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        hC.melnikovFormation.formation)
  have h := congrArg
    (fun S : Subgroup f.toMonoidHom.range => S.map f.toMonoidHom.range.subtype) hrange
  rw [Subgroup.map_map] at h
  change (proCResidualCore C G).map
      (f.toMonoidHom.range.subtype.comp f.toMonoidHom.rangeRestrict) = _ at h
  rwa [MonoidHom.subtype_comp_rangeRestrict] at h

variable {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [CompactSpace G'] [T2Space G'] [TotallyDisconnectedSpace G']

/-- Equal original images have equal images of the residual cores, even
when the original compact source groups are different. -/
theorem map_proCResidualCore_eq_of_range_eq
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H) (g : G' →ₜ* H)
    (himage : f.toMonoidHom.range = g.toMonoidHom.range) :
    (proCResidualCore C G).map f.toMonoidHom =
      (proCResidualCore C G').map g.toMonoidHom := by
  have h := congrArg
    (fun I : Subgroup H => (proCResidualCore C I).map I.subtype) himage
  exact (map_proCResidualCore_eq_rangeCore hC f).trans
    (h.trans (map_proCResidualCore_eq_rangeCore hC g).symm)

end Images

end ProCGroups.ProC
