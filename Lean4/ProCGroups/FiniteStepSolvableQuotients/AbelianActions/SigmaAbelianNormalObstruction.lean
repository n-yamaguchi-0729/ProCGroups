/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.ProC.MaximalQuotients.ResidualSigmaPower
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport

set_option autoImplicit false

/-!
# Abelian normal subgroups obstruct Sigma-faithfulness

An abelian normal subgroup meeting a prime-order relative quotient nontrivially
acts trivially on the residual abelianization when that prime is excluded.
The commutator power identity and the required power injectivity are proved
for the actual subgroup, quotient and conjugation maps.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian
open scoped IsMulCommutative

universe u

/-- A prime-order finite quotient detected by an abelian normal subgroup
prevents Sigma-abelianization-faithfulness when its prime is excluded. -/
theorem not_isSigmaAbFaithful_of_abelian_normal_prime_quotient
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (r : ℕ) [Fact r.Prime] (hr : r ∉ sigma)
    (I : Subgroup G) [I.Normal] [IsMulCommutative I]
    (N : OpenNormalSubgroup G)
    (hcard : Nat.card (G ⧸ (N : Subgroup G)) = r)
    (hI : ¬ I ≤ (N : Subgroup G)) :
    ¬ IsSigmaAbFaithful sigma G := by
  intro hG
  let hC : FiniteGroupClass.FullFormation (FiniteGroupClass.sigmaGroup.{u} sigma) :=
    FiniteGroupClass.sigmaGroup_fullFormation sigma
  have hfaith : Function.Injective
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
  have : CompactSpace (N : Subgroup G) :=
    N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let R : Subgroup (N : Subgroup G) :=
    proCResidualCore (FiniteGroupClass.sigmaGroup sigma) (N : Subgroup G)
  let A := TopologicalAbelianization ((N : Subgroup G) ⧸ R)
  let q : (N : Subgroup G) →* A :=
    (TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R)).comp (QuotientGroup.mk' R)
  have hpowinj : Function.Injective (fun a : A => a ^ r) :=
    residualAbelianization_pow_left_injective_of_prime_not_mem (N : Subgroup G) r hr
  apply hI
  intro t htI
  have htr : t ^ r ∈ (N : Subgroup G) := by
    apply (QuotientGroup.eq_one_iff (N := (N : Subgroup G)) (t ^ r)).mp
    change QuotientGroup.mk' (N : Subgroup G) (t ^ r) = 1
    rw [map_pow, ← hcard]
    exact pow_card_eq_one'
  let tr : (N : Subgroup G) := ⟨t ^ r, htr⟩
  have hqconj (n : (N : Subgroup G)) : q (MulAut.conjNormal t n) = q n := by
    let c : (N : Subgroup G) := MulAut.conjNormal t n / n
    let uI : I :=
      ⟨(n : G) * t⁻¹ * (n : G)⁻¹,
        (inferInstance : I.Normal).conj_mem t⁻¹ (I.inv_mem htI) (n : G)⟩
    have hcomm : Commute t ((n : G) * t⁻¹ * (n : G)⁻¹) := by
      change t * ((n : G) * t⁻¹ * (n : G)⁻¹) =
        ((n : G) * t⁻¹ * (n : G)⁻¹) * t
      exact congrArg (fun z : I => (z : G)) (mul_comm (⟨t, htI⟩ : I) uI)
    have hupow : ((n : G) * t⁻¹ * (n : G)⁻¹) ^ r =
        (n : G) * (t ^ r)⁻¹ * (n : G)⁻¹ := by
      simpa only [MulAut.conj_apply, inv_pow] using
        (map_pow (MulAut.conj (n : G)) t⁻¹ r).symm
    have hcpow : c ^ r = tr * n * tr⁻¹ * n⁻¹ := by
      apply Subtype.ext
      change ((t * (n : G) * t⁻¹) / (n : G)) ^ r =
        t ^ r * (n : G) * (t ^ r)⁻¹ * (n : G)⁻¹
      calc
        ((t * (n : G) * t⁻¹) / (n : G)) ^ r =
            (t * ((n : G) * t⁻¹ * (n : G)⁻¹)) ^ r := by
          simp only [div_eq_mul_inv, mul_assoc]
        _ = t ^ r * ((n : G) * t⁻¹ * (n : G)⁻¹) ^ r := hcomm.mul_pow r
        _ = t ^ r * (n : G) * (t ^ r)⁻¹ * (n : G)⁻¹ := by
          rw [hupow]
          simp only [mul_assoc]
    have hcp : (q c) ^ r = 1 := by
      rw [← map_pow, hcpow]
      simp only [map_mul, map_inv]
      rw [mul_comm (q tr) (q n), mul_assoc (q n) (q tr) (q tr)⁻¹,
        mul_inv_cancel, mul_one, mul_inv_cancel]
    have hc : q c = 1 := hpowinj (by simpa only [one_pow] using hcp)
    exact div_eq_one.mp (by simpa only [c, map_div] using hc)
  by_contra htN
  apply (residualAbelianizationQuotientConjugation_injective_iff
    hC (N : Subgroup G) N.isClosed).mp hfaith t htN
  apply MulEquiv.ext
  intro a
  refine Quotient.inductionOn' a ?_
  intro z
  refine Quotient.inductionOn' z ?_
  intro n
  change TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv hC (N : Subgroup G) N.isClosed t)
      (TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R) (QuotientGroup.mk' R n)) =
    TopologicalAbelianization.mk ((N : Subgroup G) ⧸ R) (QuotientGroup.mk' R n)
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk]
  exact hqconj n

end ProCGroups.FiniteStepSolvableQuotients
