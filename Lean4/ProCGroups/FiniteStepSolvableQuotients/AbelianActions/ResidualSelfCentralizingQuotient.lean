import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.ResidualFiniteInvariantQuotient
import ProCGroups.Abelian.FiniteInvariantQuotients
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.FiniteGroups.Classes
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Self-centralizing quotients with residual image in the formation

A faithful finite invariant quotient of the residual abelianization gives
an open normal ambient kernel. Its subgroup image is abelian and
self-centralizing. The first isomorphism theorem identifies that actual
image with the constructed finite quotient, so the image belongs to the
formation without imposing a condition on the entire ambient quotient.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

variable {C : FiniteGroupClass.{u}}
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
variable (hC : FiniteGroupClass.FullFormation C) (N : OpenNormalSubgroup H)

local notation "Res" => (N : Subgroup H) ⧸ proCResidualCore C (N : Subgroup H)
local notation "Ab" => TopologicalAbelianization Res
local notation "ρ" => residualAbelianizationQuotientConjugation hC
  (N : Subgroup H) N.isClosed
local notation "hρ" => continuous_residualAbelianizationQuotientConjugation hC
  (N : Subgroup H) N.isClosed

/-- On the original subgroup, equality in the ambient quotient is precisely
 equality in the constructed finite invariant residual quotient. -/
theorem invariantResidualAbelianQuotientKernel_mk_eq_iff
    (U : OpenNormalSubgroup Ab) (n m : (N : Subgroup H)) :
    QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (n : H) =
      QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (m : H) ↔
      invariantResidualAbelianQuotientMap hC N U n =
        invariantResidualAbelianQuotientMap hC N U m := by
  change ((n : H) : H ⧸ (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)) =
      ((m : H) : H ⧸ (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)) ↔ _
  rw [QuotientGroup.eq]
  change ((n⁻¹ * m : (N : Subgroup H)) : H) ∈
    invariantResidualAbelianQuotientKernel hC N U ↔ _
  rw [mem_invariantResidualAbelianQuotientKernel_iff, map_mul, map_inv, inv_mul_eq_one]

/-- The original subgroup has abelian image in the constructed ambient quotient. -/
theorem invariantResidualAbelianQuotientKernel_commute
    (U : OpenNormalSubgroup Ab) (n m : (N : Subgroup H)) :
    Commute
      (QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (n : H))
      (QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (m : H)) := by
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul]
  apply (invariantResidualAbelianQuotientKernel_mk_eq_iff hC N U (n * m) (m * n)).mpr
  rw [map_mul, map_mul, mul_comm]

/-- Faithfulness on the finite invariant quotient forces every ambient
 element centralizing the subgroup image to lie in the original subgroup. -/
theorem mem_of_invariantResidualAbelianQuotientKernel_centralizes
    (U : OpenNormalSubgroup Ab)
    (hfaithful : Function.Injective (invariantOpenNormalQuotientAction ρ hρ U))
    (h : H)
    (hcentralizes : ∀ n : (N : Subgroup H), Commute
      (QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H) h)
      (QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (n : H))) :
    h ∈ N := by
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup H)) h).mp
  apply hfaithful
  rw [map_one]
  apply MulEquiv.ext
  intro a
  obtain ⟨n, rfl⟩ := invariantResidualAbelianQuotientMap_surjective hC N U a
  rw [MulAut.one_apply]
  refine (invariantResidualAbelianQuotientMap_conj hC N U h n).symm.trans ?_
  apply (invariantResidualAbelianQuotientKernel_mk_eq_iff hC N U
    (MulAut.conjNormal h n) n).mp
  change QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
    (h * (n : H) * h⁻¹) = _
  rw [map_mul, map_mul, map_inv, (hcentralizes n).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- The subgroup image belongs to the formation whenever the constructed
 finite invariant quotient does: their kernels agree and both identify
 with the same quotient of the original subgroup. -/
theorem invariantResidualAbelianQuotientKernel_range_mem
    (U : OpenNormalSubgroup Ab)
    (hU : C (Ab ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup Ab))) :
    C (((ProC.OpenNormalSubgroup.quotientProj
      (invariantResidualAbelianQuotientKernel hC N U)).toMonoidHom.comp
        (N : Subgroup H).subtype).range) := by
  let A : Type u := Ab ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup Ab)
  let f : (N : Subgroup H) →* A :=
    (invariantResidualAbelianQuotientMap hC N U).toMonoidHom
  let ψ : (N : Subgroup H) →*
      H ⧸ (invariantResidualAbelianQuotientKernel hC N U : Subgroup H) :=
    (ProC.OpenNormalSubgroup.quotientProj
      (invariantResidualAbelianQuotientKernel hC N U)).toMonoidHom.comp
        (N : Subgroup H).subtype
  have hker : f.ker = ψ.ker := by
    apply Subgroup.ext
    intro n
    change invariantResidualAbelianQuotientMap hC N U n = 1 ↔
      QuotientGroup.mk' (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)
        (n : H) = 1
    exact (mem_invariantResidualAbelianQuotientKernel_iff hC N U n).symm.trans
      (QuotientGroup.eq_one_iff
        (N := (invariantResidualAbelianQuotientKernel hC N U : Subgroup H)) (n : H)).symm
  let e : A ≃* ψ.range :=
    ((QuotientGroup.quotientKerEquivOfSurjective f
      (invariantResidualAbelianQuotientMap_surjective hC N U)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivRange ψ)
  exact C.mem_of_mulEquiv e hU

/-- Faithful residual conjugation produces an open normal ambient quotient
 in which the original subgroup has abelian self-centralizing image in
 the formation. The ambient quotient itself need not belong to the class. -/
theorem exists_openNormal_abelian_selfCentralizing_quotient_inClass
    (hfaithful : Function.Injective ρ) :
    ∃ R : OpenNormalSubgroup H, (R : Subgroup H) ≤ (N : Subgroup H) ∧
      C (((ProC.OpenNormalSubgroup.quotientProj R).toMonoidHom.comp
        (N : Subgroup H).subtype).range) ∧
      (∀ n m : (N : Subgroup H), Commute
        (QuotientGroup.mk' (R : Subgroup H) (n : H))
        (QuotientGroup.mk' (R : Subgroup H) (m : H))) ∧
      (∀ h : H, (∀ n : (N : Subgroup H), Commute
        (QuotientGroup.mk' (R : Subgroup H) h)
        (QuotientGroup.mk' (R : Subgroup H) (n : H))) → h ∈ N) := by
  obtain ⟨U, hUfaithful, hUclass⟩ :=
    exists_faithful_invariantResidualAbelianQuotient hC N hfaithful
  exact ⟨invariantResidualAbelianQuotientKernel hC N U,
    invariantResidualAbelianQuotientKernel_le hC N U,
    invariantResidualAbelianQuotientKernel_range_mem hC N U hUclass,
    invariantResidualAbelianQuotientKernel_commute hC N U,
    mem_of_invariantResidualAbelianQuotientKernel_centralizes hC N U hUfaithful⟩

end ProCGroups.FiniteStepSolvableQuotients
