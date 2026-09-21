import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.EmbeddingFormulation
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.FiniteGroups.Classes
import ProCGroups.ProC.InverseLimits.FiniteQuotients
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.MaximalQuotients.UniversalProperty
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Self-centralizing finite images detect residual conjugation

A homomorphism with finite image in a full formation factors through the
actual residual quotient. If its image is commutative, equality after
topological abelianization of that quotient forces equality in the image.
Consequently, a self-centralizing such image of an open normal subgroup
detects the residual quotient conjugation action. Only the subgroup image,
and not the entire ambient target, is required to belong to the formation.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Equality in the abelianized residual quotient is detected by every
continuous homomorphism with commutative finite image in the formation. -/
theorem map_eq_of_residualTopologicalAbelianization_eq [CompactSpace H]
    (hC : FiniteGroupClass.FullFormation C)
    {D : Type u} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (f : H →ₜ* D) (hImage : C f.toMonoidHom.range)
    (hcomm : ∀ x y : H, Commute (f x) (f y))
    {x y : H}
    (hxy : TopologicalAbelianization.mk (H ⧸ proCResidualCore C H)
        (QuotientGroup.mk' (proCResidualCore C H) x) =
      TopologicalAbelianization.mk (H ⧸ proCResidualCore C H)
        (QuotientGroup.mk' (proCResidualCore C H) y)) :
    f x = f y := by
  have : Finite f.toMonoidHom.range := C.finite_of_mem hImage
  let fr : H →ₜ* f.toMonoidHom.range :=
    { toMonoidHom := f.toMonoidHom.rangeRestrict
      continuous_toFun := f.continuous_toFun.subtype_mk
        (fun z => ⟨z, rfl⟩) }
  have hRange : HasOpenNormalBasisInClass C f.toMonoidHom.range :=
    HasOpenNormalBasisInClass.of_finite_discrete
      hC.melnikovFormation.formation.quotientClosed hImage
  let fbar : H ⧸ proCResidualCore C H →ₜ* f.toMonoidHom.range :=
    lift_proCResidualCoreQuotient hC.hereditary fr hRange
  have hbar_mk (z : H) :
      fbar (QuotientGroup.mk' (proCResidualCore C H) z) = fr z :=
    lift_proCResidualCoreQuotient_mk hC.hereditary fr hRange z
  have hbar_comm : ∀ a b : H ⧸ proCResidualCore C H,
      Commute (fbar a) (fbar b) := by
    intro a b
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C H) a
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C H) b
    rw [hbar_mk, hbar_mk]
    change fr z * fr w = fr w * fr z
    apply Subtype.ext
    exact (hcomm z w).eq
  have hfr : fr x = fr y :=
    (hbar_mk x).symm.trans
      ((map_eq_of_topologicalAbelianization_eq fbar hbar_comm hxy).trans (hbar_mk y))
  exact congrArg Subtype.val hfr

/-- A commutative finite image in the formation, whose ambient centralizer
has preimage contained in `N`, makes actual residual conjugation faithful. -/
theorem injective_residualQuotientConjugation_of_selfCentralizing_image
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : FiniteGroupClass.FullFormation C)
    {D : Type u} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (N : OpenNormalSubgroup H) (θ : H →ₜ* D)
    (hImage : C (θ.toMonoidHom.comp (N : Subgroup H).subtype).range)
    (hcomm : ∀ n m : (N : Subgroup H), Commute
      (θ (n : H)) (θ (m : H)))
    (hcentralizer : ∀ h : H, (∀ n : (N : Subgroup H), Commute
      (θ h) (θ (n : H))) → h ∈ N) :
    Function.Injective
      (residualAbelianizationQuotientConjugation hC (N : Subgroup H) N.isClosed) := by
  have : CompactSpace (N : Subgroup H) :=
    N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  apply (injective_iff_map_eq_one
    (residualAbelianizationQuotientConjugation hC (N : Subgroup H) N.isClosed)).mpr
  intro q hq
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (N : Subgroup H) q
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup H)) h).mpr
  apply hcentralizer h
  intro n
  let f : (N : Subgroup H) →ₜ* D :=
    { toMonoidHom := θ.toMonoidHom.comp (N : Subgroup H).subtype
      continuous_toFun := θ.continuous_toFun.comp continuous_subtype_val }
  rw [residualAbelianizationQuotientConjugation_mk] at hq
  have hab := DFunLike.congr_fun hq
    (TopologicalAbelianization.mk
      ((N : Subgroup H) ⧸ proCResidualCore C (N : Subgroup H))
      (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) n))
  change TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv hC (N : Subgroup H) N.isClosed h)
      (TopologicalAbelianization.mk
        ((N : Subgroup H) ⧸ proCResidualCore C (N : Subgroup H))
        (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) n)) =
    TopologicalAbelianization.mk
      ((N : Subgroup H) ⧸ proCResidualCore C (N : Subgroup H))
      (QuotientGroup.mk' (proCResidualCore C (N : Subgroup H)) n) at hab
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk] at hab
  have hf : f (MulAut.conjNormal h n) = f n :=
    map_eq_of_residualTopologicalAbelianization_eq hC f hImage hcomm hab
  change θ (h * (n : H) * h⁻¹) = θ (n : H) at hf
  rw [map_mul, map_mul, map_inv] at hf
  exact (mul_inv_eq_iff_eq_mul).mp hf

end ProCGroups.FiniteStepSolvableQuotients
