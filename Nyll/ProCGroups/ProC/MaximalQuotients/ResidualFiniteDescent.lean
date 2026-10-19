/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.Classes
import Nyll.ProCGroups.Profinite.OpenSubgroups
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Nyll.ProCGroups.Topologies.QuotientMaps
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite-quotient descent and maximal pro-C quotients

The residual core is detected by the actual continuous finite quotients
whose groups lie in `C`. For a continuous epimorphism `f`, containment of
its kernel in this core is equivalent to unique continuous descent of all
these finite quotient maps. We also construct the map on the actual
residual quotients and prove that its bijectivity is equivalent to this
finite-quotient descent property.

This is the group-theoretic criterion used after extension of finite Galois
covers in Stacks Project, Theorem 58.30.3 (tag `0C0R`). These are statements
about arbitrary continuous group maps; no geometric extension or
specialization assertion is assumed or concluded.
-/

namespace ProCGroups.ProC

universe u

section Detection

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- Membership in the residual core is detected by surjective continuous
maps to finite discrete groups in the specified full formation. -/
theorem mem_proCResidualCore_iff_finite_quotients
    (hC : FiniteGroupClass.FullFormation C) (g : G) :
    g ∈ proCResidualCore C G ↔
      ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q],
        C Q → ∀ (q : G →ₜ* Q), Function.Surjective q → q g = 1 := by
  constructor
  · intro hg Q _ _ _ hQ q _
    have : Finite Q := C.finite hQ
    have hQbasis : HasOpenNormalBasisInClass C Q :=
      HasOpenNormalBasisInClass.of_finite_discrete
        hC.melnikovFormation.formation.quotientClosed hQ
    exact proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
      hC.hereditary q hQbasis hg
  · intro hg
    rw [proCResidualCore, Subgroup.mem_sInf]
    rintro N ⟨U, rfl⟩
    have : IsClosed (U.toSubgroup : Set G) := U.isClosed'
    let projection : G →ₜ* G ⧸ U.toSubgroup :=
      { toMonoidHom := QuotientGroup.mk' U.toSubgroup
        continuous_toFun := QuotientGroup.continuous_mk }
    apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) g).mp
    apply U.quotient_hasOpenNormalBasisInClass.eq_one_of_mem_all_openNormalSubgroupInClass
    intro V
    let Q : Type u := (G ⧸ U.toSubgroup) ⧸ (V.1 : Subgroup (G ⧸ U.toSubgroup))
    have : DiscreteTopology Q :=
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := G ⧸ U.toSubgroup) V.1)
    let q : G →ₜ* Q := (OpenNormalSubgroupInClass.quotientProj V).comp projection
    have hq : Function.Surjective q :=
      (OpenNormalSubgroupInClass.quotientProj_surjective V).comp
        (QuotientGroup.mk'_surjective U.toSubgroup)
    exact OpenNormalSubgroupInClass.quotientProj_eq_one_iff.mp (hg Q V.2 q hq)

variable {H : Type u} [Group H] [TopologicalSpace H] [T2Space H]

/-- For a continuous epimorphism from a compact group, having kernel in the
residual core is equivalent to unique continuous descent of every finite
quotient belonging to `C`. -/
theorem ker_le_proCResidualCore_iff_finite_quotient_descent
    (hC : FiniteGroupClass.FullFormation C)
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    f.toMonoidHom.ker ≤ proCResidualCore C G ↔
      ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q],
        C Q → ∀ (q : G →ₜ* Q), Function.Surjective q →
          ∃! r : H →ₜ* Q, r.comp f = q := by
  constructor
  · intro hker Q _ _ _ hQ q _
    have : Finite Q := C.finite hQ
    have hQbasis : HasOpenNormalBasisInClass C Q :=
      HasOpenNormalBasisInClass.of_finite_discrete
        hC.melnikovFormation.formation.quotientClosed hQ
    have hqker : f.toMonoidHom.ker ≤ q.toMonoidHom.ker :=
      hker.trans (proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
        hC.hereditary q hQbasis)
    let rAlg : H →* Q :=
      f.toMonoidHom.liftOfSurjective hf ⟨q.toMonoidHom, hqker⟩
    have hrAlg : rAlg.comp f.toMonoidHom = q.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact MonoidHom.liftOfRightInverse_comp_apply
        (f := f.toMonoidHom) (f_inv := Function.surjInv hf)
        (Function.rightInverse_surjInv hf) ⟨q.toMonoidHom, hqker⟩ x
    have hrcont : Continuous rAlg := by
      apply (Topology.IsQuotientMap.of_surjective_continuous
        hf f.continuous_toFun).continuous_iff.mpr
      convert q.continuous_toFun using 1
      funext x
      exact DFunLike.congr_fun hrAlg x
    let r : H →ₜ* Q := ⟨rAlg, hrcont⟩
    have hr : r.comp f = q := by
      apply ContinuousMonoidHom.ext
      intro x
      exact DFunLike.congr_fun hrAlg x
    refine ⟨r, hr, ?_⟩
    intro r' hr'
    apply ContinuousMonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact (DFunLike.congr_fun hr' x).trans (DFunLike.congr_fun hr x).symm
  · intro hdescent g hg
    apply (mem_proCResidualCore_iff_finite_quotients hC g).mpr
    intro Q _ _ _ hQ q hq
    obtain ⟨r, hr, _⟩ := hdescent Q hQ q hq
    have heq : r (f g) = q g := DFunLike.congr_fun hr g
    change f g = 1 at hg
    rw [hg, map_one] at heq
    exact heq.symm

end Detection

section Map

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H]

/-- A continuous map induces the map on the actual pro-C residual quotients.
Its descent condition follows from functoriality of the residual core. -/
noncomputable def residualQuotientMap
    (hC : FiniteGroupClass.Hereditary C) (f : G →ₜ* H) :
    G ⧸ proCResidualCore C G →ₜ* H ⧸ proCResidualCore C H :=
  QuotientGroup.mapₜ (proCResidualCore C G) (proCResidualCore C H) f (by
    intro x hx
    exact map_proCResidualCore_le_of_continuousMonoidHom hC f ⟨x, hx, rfl⟩)

/-- The residual-quotient map applies the original map to a representative. -/
@[simp] theorem residualQuotientMap_apply_mk
    (hC : FiniteGroupClass.Hereditary C) (f : G →ₜ* H) (x : G) :
    residualQuotientMap hC f (QuotientGroup.mk' (proCResidualCore C G) x) =
      QuotientGroup.mk' (proCResidualCore C H) (f x) :=
  QuotientGroup.mapₜ_apply_mk _ _ _ _ x

/-- The map induced on residual quotients by a continuous epimorphism is
surjective. -/
theorem residualQuotientMap_surjective
    (hC : FiniteGroupClass.Hereditary C) (f : G →ₜ* H)
    (hf : Function.Surjective f) :
    Function.Surjective (residualQuotientMap hC f) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C H) q
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨QuotientGroup.mk' (proCResidualCore C G) g,
    residualQuotientMap_apply_mk hC f g⟩

variable [T2Space G] [TotallyDisconnectedSpace G]

/-- For a continuous epimorphism of profinite groups, injectivity of the
induced residual-quotient map is exactly the residual-core kernel condition. -/
theorem residualQuotientMap_injective_iff_ker_le
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H)
    (hf : Function.Surjective f) :
    Function.Injective (residualQuotientMap hC.hereditary f) ↔
      f.toMonoidHom.ker ≤ proCResidualCore C G := by
  constructor
  · intro hinj g hg
    apply (QuotientGroup.eq_one_iff (N := proCResidualCore C G) g).mp
    apply hinj
    rw [← QuotientGroup.mk'_apply (proCResidualCore C G) g,
      residualQuotientMap_apply_mk, show f g = 1 from hg, map_one, map_one]
  · intro hker
    have hmap : (proCResidualCore C G).map f.toMonoidHom = proCResidualCore C H :=
      map_proCResidualCore_eq_of_surjective hC f.toMonoidHom f.continuous_toFun hf
        (proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation)
    have hcomap : (proCResidualCore C H).comap f.toMonoidHom = proCResidualCore C G :=
      QuotientGroup.comap_eq_of_map_eq_of_ker_le f.toMonoidHom hmap hker
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C G) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C G) b
    apply (QuotientGroup.eq_iff_div_mem (N := proCResidualCore C G)).mpr
    have himage : f (x / y) ∈ proCResidualCore C H := by
      rw [map_div]
      apply (QuotientGroup.eq_iff_div_mem (N := proCResidualCore C H)).mp
      have hquot : QuotientGroup.mk' (proCResidualCore C H) (f x) =
          QuotientGroup.mk' (proCResidualCore C H) (f y) :=
        (residualQuotientMap_apply_mk hC.hereditary f x).symm.trans
          (hab.trans (residualQuotientMap_apply_mk hC.hereditary f y))
      exact (QuotientGroup.mk'_apply (proCResidualCore C H) (f x)).symm.trans
        (hquot.trans (QuotientGroup.mk'_apply (proCResidualCore C H) (f y)))
    change x / y ∈ (proCResidualCore C H).comap f.toMonoidHom at himage
    rw [hcomap] at himage
    exact himage

/-- The actual induced pro-C map of a continuous epimorphism is bijective
exactly when every finite C quotient descends uniquely and continuously. -/
theorem residualQuotientMap_bijective_iff_finite_quotient_descent
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H)
    (hf : Function.Surjective f) :
    Function.Bijective (residualQuotientMap hC.hereditary f) ↔
      ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q],
        C Q → ∀ (q : G →ₜ* Q), Function.Surjective q →
          ∃! r : H →ₜ* Q, r.comp f = q := by
  constructor
  · intro h
    exact (ker_le_proCResidualCore_iff_finite_quotient_descent hC f hf).mp
      ((residualQuotientMap_injective_iff_ker_le hC f hf).mp h.1)
  · intro h
    refine ⟨?_, residualQuotientMap_surjective hC.hereditary f hf⟩
    exact (residualQuotientMap_injective_iff_ker_le hC f hf).mpr
      ((ker_le_proCResidualCore_iff_finite_quotient_descent hC f hf).mpr h)

/-- A finite-quotient descent proof constructs a topological group
equivalence whose forward map is the actual induced residual-quotient map. -/
noncomputable def residualQuotientEquivOfFiniteQuotientDescent
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H)
    (hf : Function.Surjective f)
    (hdescent : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q],
      C Q → ∀ (q : G →ₜ* Q), Function.Surjective q →
        ∃! r : H →ₜ* Q, r.comp f = q) :
    G ⧸ proCResidualCore C G ≃ₜ* H ⧸ proCResidualCore C H := by
  have : IsClosed ((proCResidualCore C H : Subgroup H) : Set H) :=
    proCResidualCore_isClosed C H
  exact ContinuousMulEquiv.ofBijectiveCompactToT2
    (residualQuotientMap hC.hereditary f).toMonoidHom
    (residualQuotientMap hC.hereditary f).continuous_toFun
    ((residualQuotientMap_bijective_iff_finite_quotient_descent hC f hf).mpr hdescent)

/-- The constructed equivalence keeps the representative-level map `f`. -/
@[simp] theorem residualQuotientEquivOfFiniteQuotientDescent_apply_mk
    (hC : FiniteGroupClass.FullFormation C) (f : G →ₜ* H)
    (hf : Function.Surjective f)
    (hdescent : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q],
      C Q → ∀ (q : G →ₜ* Q), Function.Surjective q →
        ∃! r : H →ₜ* Q, r.comp f = q) (g : G) :
    residualQuotientEquivOfFiniteQuotientDescent hC f hf hdescent
        (QuotientGroup.mk' (proCResidualCore C G) g) =
      QuotientGroup.mk' (proCResidualCore C H) (f g) :=
  residualQuotientMap_apply_mk hC.hereditary f g

end Map

end ProCGroups.ProC
