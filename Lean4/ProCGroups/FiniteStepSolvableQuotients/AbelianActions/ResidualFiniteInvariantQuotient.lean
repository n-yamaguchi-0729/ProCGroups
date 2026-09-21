import ProCGroups.Abelian.FiniteInvariantQuotients
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.ProC.Quotients.ClosedNormal
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Finite invariant quotients of residual abelianizations

A faithful finite relative action on the actual residual abelianization
admits a faithful finite invariant quotient in the original formation.
Pulling its projection back to the normal subgroup produces an open normal
subgroup of the ambient group. In particular, the class of finite Sigma
groups gives finite abelian Sigma quotients with an actual ambient kernel.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

variable {C : FiniteGroupClass.{u}}
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Each automorphism in residual quotient conjugation is continuous. -/
theorem continuous_residualAbelianizationQuotientConjugation
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup H) [N.Normal] (hN : IsClosed (N : Set H)) (q : H ⧸ N) :
    Continuous (residualAbelianizationQuotientConjugation hC N hN q) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
  change Continuous (TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hC N hN h) :
      TopologicalAbelianization (N ⧸ proCResidualCore C N) →
        TopologicalAbelianization (N ⧸ proCResidualCore C N))
  exact (TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hC N hN h)).continuous_toFun

variable (hC : FiniteGroupClass.FullFormation C) (N : OpenNormalSubgroup H)

local notation "Res" => (N : Subgroup H) ⧸ proCResidualCore C (N : Subgroup H)
local notation "Ab" => TopologicalAbelianization Res
local notation "ρ" => residualAbelianizationQuotientConjugation hC
  (N : Subgroup H) N.isClosed
local notation "hρ" => continuous_residualAbelianizationQuotientConjugation hC
  (N : Subgroup H) N.isClosed

/-- The projection to the finite invariant residual abelian quotient, pulled
back along the two canonical quotient maps from the original subgroup. -/
noncomputable def invariantResidualAbelianQuotientMap (U : OpenNormalSubgroup Ab) :
    (N : Subgroup H) →ₜ* Ab ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup Ab) :=
  (ProC.OpenNormalSubgroup.quotientProj (invariantOpenNormalCore ρ hρ U)).comp
    ((TopologicalAbelianization.mkₜ Res).comp
      { toMonoidHom := QuotientGroup.mk' (proCResidualCore C (N : Subgroup H))
        continuous_toFun := QuotientGroup.continuous_mk })

/-- The composite is the actual residual and abelianization projection on
every subgroup representative. -/
theorem invariantResidualAbelianQuotientMap_apply
    (U : OpenNormalSubgroup Ab) (n : (N : Subgroup H)) :
    invariantResidualAbelianQuotientMap hC N U n =
      QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup Ab)
        (TopologicalAbelianization.mk Res
          (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) n)) := by
  rfl

/-- The composite onto the finite invariant quotient is surjective. -/
theorem invariantResidualAbelianQuotientMap_surjective
    (U : OpenNormalSubgroup Ab) :
    Function.Surjective (invariantResidualAbelianQuotientMap hC N U) := by
  intro a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (invariantOpenNormalCore ρ hρ U : Subgroup Ab) a
  obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk Res b
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    (proCResidualCore C (N : Subgroup H)) z
  exact ⟨n, invariantResidualAbelianQuotientMap_apply hC N U n⟩

/-- The composite preserves the actual ambient conjugation action. -/
theorem invariantResidualAbelianQuotientMap_conj
    (U : OpenNormalSubgroup Ab) (h : H) (n : (N : Subgroup H)) :
    invariantResidualAbelianQuotientMap hC N U (MulAut.conjNormal h n) =
      invariantOpenNormalQuotientAction ρ hρ U
        (QuotientGroup.mk' (N : Subgroup H) h)
        (invariantResidualAbelianQuotientMap hC N U n) := by
  rw [invariantResidualAbelianQuotientMap_apply,
    invariantResidualAbelianQuotientMap_apply,
    invariantOpenNormalQuotientAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup Ab))
  change TopologicalAbelianization.mk Res
    (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) (MulAut.conjNormal h n)) =
      TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC (N : Subgroup H) N.isClosed h)
        (TopologicalAbelianization.mk Res
          (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) n))
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk]

/-- The finite invariant quotient has an actual open normal kernel in the
ambient group; normality follows from the constructed conjugation formula. -/
noncomputable def invariantResidualAbelianQuotientKernel
    (U : OpenNormalSubgroup Ab) : OpenNormalSubgroup H where
  toSubgroup := (invariantResidualAbelianQuotientMap hC N U).toMonoidHom.ker.map
    (N : Subgroup H).subtype
  isOpen' := by
    exact N.isOpen'.isOpenMap_subtype_val
      ((invariantResidualAbelianQuotientMap hC N U).toMonoidHom.ker : Set (N : Subgroup H))
      (ProC.OpenNormalSubgroup.ker (invariantResidualAbelianQuotientMap hC N U)).isOpen'
  isNormal' := by
    refine ⟨?_⟩
    intro x hx h
    obtain ⟨n, hn, rfl⟩ := hx
    refine ⟨MulAut.conjNormal h n, ?_, MulAut.conjNormal_apply h n⟩
    change invariantResidualAbelianQuotientMap hC N U (MulAut.conjNormal h n) = 1
    change invariantResidualAbelianQuotientMap hC N U n = 1 at hn
    rw [invariantResidualAbelianQuotientMap_conj, hn, map_one]

/-- The ambient kernel is contained in the original open normal subgroup. -/
theorem invariantResidualAbelianQuotientKernel_le
    (U : OpenNormalSubgroup Ab) :
    (invariantResidualAbelianQuotientKernel hC N U : Subgroup H) ≤ (N : Subgroup H) := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact n.property

/-- Restricting the ambient kernel back to the original subgroup recovers
exactly the kernel of the finite quotient map. -/
theorem mem_invariantResidualAbelianQuotientKernel_iff
    (U : OpenNormalSubgroup Ab) (n : (N : Subgroup H)) :
    (n : H) ∈ invariantResidualAbelianQuotientKernel hC N U ↔
      invariantResidualAbelianQuotientMap hC N U n = 1 := by
  constructor
  · intro hn
    obtain ⟨m, hm, hmn⟩ := hn
    have heq : m = n := Subtype.ext hmn
    exact heq ▸ hm
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- A faithful action on the residual abelianization admits a faithful finite
invariant quotient in the same formation. For `sigmaGroup sigma`, this is a
finite abelian Sigma group, with the ambient kernel constructed above. -/
theorem exists_faithful_invariantResidualAbelianQuotient
    (hfaithful : Function.Injective ρ) :
    ∃ U : OpenNormalSubgroup Ab,
      Function.Injective (invariantOpenNormalQuotientAction ρ hρ U) ∧
        C (Ab ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup Ab)) := by
  have : CompactSpace (N : Subgroup H) :=
    N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  have hRclosed : IsClosed
      ((proCResidualCore C (N : Subgroup H) : Subgroup (N : Subgroup H)) :
        Set (N : Subgroup H)) :=
    proCResidualCore_isClosed C (N : Subgroup H)
  have : TotallyDisconnectedSpace Res :=
    totallyDisconnectedSpace_quotient_closedNormal
      (proCResidualCore C (N : Subgroup H)) hRclosed
  have : TotallyDisconnectedSpace Ab :=
    totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator Res) (Subgroup.isClosed_closedCommutator Res)
  have hRes : HasOpenNormalBasisInClass C Res :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation
  have hAb : HasOpenNormalBasisInClass C Ab :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation hRes
      (TopologicalAbelianization.mkₜ Res) (TopologicalAbelianization.surjective_mk Res)
  obtain ⟨U, hU⟩ := exists_faithful_invariantOpenNormalQuotientAction ρ hρ hfaithful
  exact ⟨U, hU, HasOpenNormalBasisInClass.quotient_mem hC.melnikovFormation.formation
    hAb (invariantOpenNormalCore ρ hρ U)⟩

end ProCGroups.FiniteStepSolvableQuotients
