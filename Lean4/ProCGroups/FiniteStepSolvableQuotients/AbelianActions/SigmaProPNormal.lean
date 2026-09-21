import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.ProC.MaximalQuotients.ResidualPrimeExclusion
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.Profinite.Basic

set_option autoImplicit false

/-!
# Sigma-faithfulness excludes normal pro-p subgroups

For an excluded prime, a normal pro-p subgroup acts trivially on the actual
maximal pro-Sigma quotient of every open normal subgroup. Sigma-faithfulness
puts it inside every open normal subgroup, whose intersection is trivial.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

/-- A Sigma-abelianization-faithful profinite group has no nontrivial normal
pro-p subgroup when `p` is outside Sigma. Closedness of the subgroup is unnecessary. -/
theorem IsSigmaAbFaithful.normal_proP_eq_bot
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsSigmaAbFaithful sigma G)
    (p : ℕ) [Fact p.Prime] (hp : p ∉ sigma)
    (P : Subgroup G) [P.Normal]
    (hP : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) P) :
    P = ⊥ := by
  let hC : FiniteGroupClass.FullFormation (FiniteGroupClass.sigmaGroup.{u} sigma) :=
    FiniteGroupClass.sigmaGroup_fullFormation sigma
  have hfaith (N : OpenNormalSubgroup G) :
      Function.Injective
        (residualAbelianizationQuotientConjugation hC (N : Subgroup G) N.isClosed) := by
    let H : OpenSubgroup G := ⊤
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    let e : G ≃ₜ* (H : Subgroup G) :=
      { toMulEquiv := Subgroup.topEquiv.symm
        continuous_toFun := continuous_id.subtype_mk (fun _ => Subgroup.mem_top _)
        continuous_invFun := continuous_subtype_val }
    let Nmap : OpenNormalSubgroup (H : Subgroup G) :=
      ProCGroups.ProC.OpenNormalSubgroup.map
        (ContinuousMonoidHom.toContinuousMonoidHom e)
        e.toHomeomorph.isOpenMap e.surjective N
    exact (residualAbelianizationQuotientConjugation_injective_map_iff
      hC e (N : Subgroup G) N.isClosed).mp (hG H Nmap)
  apply bot_unique
  intro g hg
  change g = 1
  apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
  intro N
  have : CompactSpace (N : Subgroup G) :=
    N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let R : Subgroup (N : Subgroup G) :=
    proCResidualCore (FiniteGroupClass.sigmaGroup sigma) (N : Subgroup G)
  have : R.Normal := proCResidualCore_normal _ _
  have : IsClosed (R : Set (N : Subgroup G)) := proCResidualCore_isClosed _ _
  have hR : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma)
      ((N : Subgroup G) ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation
  let Q : Subgroup P := (N : Subgroup G).comap P.subtype
  have hQclosed : IsClosed (Q : Set P) :=
    N.isClosed.preimage continuous_subtype_val
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) Q :=
    HasOpenNormalBasisInClass.of_isClosed_subgroup
      (FiniteGroupClass.pGroup p).isomClosed
      (FiniteGroupClass.pGroup_subgroupClosed p) hP Q hQclosed
  let incl : Q →ₜ* (N : Subgroup G) :=
    { toFun := fun z => ⟨((z : P) : G), z.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
          (fun z : Q => z.property) }
  let π : (N : Subgroup G) →ₜ* (N : Subgroup G) ⧸ R :=
    { toMonoidHom := QuotientGroup.mk' R
      continuous_toFun := continuous_quotient_mk' }
  have hdiff (n : (N : Subgroup G)) : MulAut.conjNormal g n / n ∈ R := by
    let d : (N : Subgroup G) := MulAut.conjNormal g n / n
    have hdP : (d : G) ∈ P := by
      have hc : (n : G) * g⁻¹ * (n : G)⁻¹ ∈ P :=
        (inferInstance : P.Normal).conj_mem g⁻¹ (P.inv_mem hg) (n : G)
      change (g * (n : G) * g⁻¹) / (n : G) ∈ P
      simpa only [div_eq_mul_inv, mul_assoc] using P.mul_mem hg hc
    let dQ : Q := ⟨⟨(d : G), hdP⟩, d.property⟩
    have hd : QuotientGroup.mk' R d = 1 :=
      continuousMonoidHom_eq_one_of_proP_to_proSigma p hp hQ hR (π.comp incl) dQ
    exact (QuotientGroup.eq_one_iff (N := R) d).mp hd
  by_contra hgn
  apply (residualAbelianizationQuotientConjugation_injective_iff
    hC (N : Subgroup G) N.isClosed).mp (hfaith N) g hgn
  apply MulEquiv.ext
  intro a
  refine Quotient.inductionOn' a ?_
  intro z
  refine Quotient.inductionOn' z ?_
  intro n
  change TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv hC (N : Subgroup G) N.isClosed g)
      (TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R) (QuotientGroup.mk' R n)) =
    TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R) (QuotientGroup.mk' R n)
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk]
  apply congrArg (TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R))
  exact (QuotientGroup.eq_iff_div_mem (N := R)).mpr (hdiff n)

end ProCGroups.FiniteStepSolvableQuotients
