/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.PrimeOrderTest
import ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.Abelian.TopologicalAbelianization

set_option autoImplicit false

/-!
# The prime-order test for Sigma-abelianization-faithfulness

A prime-order subgroup of the kernel of a nonfaithful quotient action pulls
back to an open layer in the original group. The two presentations of its
normal subgroup have canonically equivalent residual quotients, and the
induced equivalence on abelianizations preserves conjugation. The prime
order of the acting quotient is unrestricted by Sigma.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

private theorem exists_prime_quotient_trivial_residual_action_of_not_injective
    {C : FiniteGroupClass.{u}} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hC : FiniteGroupClass.FullFormation C)
    (H : OpenSubgroup G) [CompactSpace (H : Subgroup G)]
    (N : OpenNormalSubgroup (H : Subgroup G))
    (hρ : ¬ Function.Injective
      (residualAbelianizationQuotientConjugation hC
        (N : Subgroup (H : Subgroup G)) N.isClosed)) :
    ∃ J : OpenSubgroup G,
      letI : CompactSpace (J : Subgroup G) :=
        J.isClosed.isClosedEmbedding_subtypeVal.compactSpace
      ∃ M : OpenNormalSubgroup (J : Subgroup G),
        Nat.Prime (Nat.card ((J : Subgroup G) ⧸ (M : Subgroup (J : Subgroup G)))) ∧
        residualAbelianizationQuotientConjugation hC
          (M : Subgroup (J : Subgroup G)) M.isClosed = 1 := by
  let Q : Type u := ↥(H : Subgroup G) ⧸ (N : Subgroup ↥(H : Subgroup G))
  let π : ↥(H : Subgroup G) →ₜ* Q := ProC.OpenNormalSubgroup.quotientProj N
  let ρ : Q →* MulAut (TopologicalAbelianization
      (↥(N : Subgroup ↥(H : Subgroup G)) ⧸
        proCResidualCore C ↥(N : Subgroup ↥(H : Subgroup G)))) :=
    residualAbelianizationQuotientConjugation hC
      (N : Subgroup ↥(H : Subgroup G)) N.isClosed
  obtain ⟨S, hSprime, hSker⟩ :=
    exists_prime_card_subgroup_le_ker_of_not_injective ρ hρ
  let P : OpenSubgroup ↥(H : Subgroup G) :=
    { toSubgroup := S.comap π.toMonoidHom
      isOpen' := (isOpen_discrete (S : Set Q)).preimage π.continuous_toFun }
  let J : OpenSubgroup G :=
    { toSubgroup := (P : Subgroup ↥(H : Subgroup G)).map (H : Subgroup G).subtype
      isOpen' := H.isOpen.isOpenMap_subtype_val _ P.isOpen }
  have : CompactSpace (J : Subgroup G) :=
    J.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  have hJH : (J : Subgroup G) ≤ (H : Subgroup G) := by
    intro g hg
    obtain ⟨h, hh, hhg⟩ := hg
    exact hhg ▸ h.property
  let j : ↥(J : Subgroup G) →ₜ* ↥(H : Subgroup G) :=
    { toFun := fun g => ⟨g.val, hJH g.property⟩
      map_one' := rfl
      map_mul' := fun g k => rfl
      continuous_toFun :=
        Continuous.subtype_mk continuous_subtype_val (fun g => hJH g.property) }
  have hjP : ∀ g : ↥(J : Subgroup G), j g ∈ (P : Subgroup ↥(H : Subgroup G)) := by
    intro g
    obtain ⟨h, hh, hhg⟩ := g.property
    have heq : h = j g := Subtype.ext hhg
    exact heq ▸ hh
  let q : ↥(J : Subgroup G) →ₜ* S :=
    { toFun := fun g => ⟨π (j g), hjP g⟩
      map_one' := Subtype.ext (map_one (π.comp j))
      map_mul' := fun g k => Subtype.ext (map_mul (π.comp j) g k)
      continuous_toFun :=
        Continuous.subtype_mk (π.continuous_toFun.comp j.continuous_toFun) hjP }
  have hqsurj : Function.Surjective q := by
    intro c
    obtain ⟨h, hh⟩ := ProC.OpenNormalSubgroup.quotientProj_surjective N c.val
    have hhP : h ∈ (P : Subgroup ↥(H : Subgroup G)) := by
      change π h ∈ S
      rw [hh]
      exact c.property
    let g : ↥(J : Subgroup G) := ⟨h.val, ⟨h, hhP, rfl⟩⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hh
  let M : OpenNormalSubgroup ↥(J : Subgroup G) := ProC.OpenNormalSubgroup.ker q
  have hMcard : Nat.card (↥(J : Subgroup G) ⧸ (M : Subgroup ↥(J : Subgroup G))) =
      Nat.card S :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hqsurj).toEquiv
  have hNtoP : ∀ n : ↥(N : Subgroup ↥(H : Subgroup G)),
      n.val ∈ (P : Subgroup ↥(H : Subgroup G)) := by
    intro n
    have hn : π n.val = 1 :=
      (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).2 n.property
    change π n.val ∈ S
    rw [hn]
    exact S.one_mem
  let liftN : ↥(N : Subgroup ↥(H : Subgroup G)) → ↥(J : Subgroup G) :=
    fun n => ⟨n.val.val, ⟨n.val, hNtoP n, rfl⟩⟩
  have hliftN : ∀ n : ↥(N : Subgroup ↥(H : Subgroup G)), liftN n ∈ M := by
    intro n
    change q (liftN n) = 1
    apply Subtype.ext
    exact (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).2 n.property
  have hMtoN : ∀ m : ↥(M : Subgroup ↥(J : Subgroup G)),
      j m.val ∈ (N : Subgroup ↥(H : Subgroup G)) := by
    intro m
    apply (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).1
    exact congrArg Subtype.val (show q m.val = 1 from m.property)
  let e : ↥(M : Subgroup ↥(J : Subgroup G)) ≃ₜ*
      ↥(N : Subgroup ↥(H : Subgroup G)) :=
    { toMulEquiv :=
        { toFun := fun m => ⟨j m.val, hMtoN m⟩
          invFun := fun n => ⟨liftN n, hliftN n⟩
          left_inv := fun m => Subtype.ext (Subtype.ext rfl)
          right_inv := fun n => Subtype.ext (Subtype.ext rfl)
          map_mul' := fun m k => Subtype.ext (map_mul j m.val k.val) }
      continuous_toFun :=
        Continuous.subtype_mk (j.continuous_toFun.comp continuous_subtype_val) hMtoN
      continuous_invFun :=
        Continuous.subtype_mk
          (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
            (fun n => ⟨n.val, hNtoP n, rfl⟩)) hliftN }
  have : CompactSpace (N : Subgroup (H : Subgroup G)) :=
    N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  have : CompactSpace (M : Subgroup (J : Subgroup G)) :=
    M.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let t : TopologicalAbelianization
      (↥(M : Subgroup (J : Subgroup G)) ⧸
        proCResidualCore C ↥(M : Subgroup (J : Subgroup G))) ≃ₜ*
      TopologicalAbelianization
        (↥(N : Subgroup (H : Subgroup G)) ⧸
          proCResidualCore C ↥(N : Subgroup (H : Subgroup G))) :=
    TopologicalAbelianization.congr (residualQuotientContinuousMulEquiv hC.hereditary e)
  refine ⟨J, M, hMcard.symm ▸ hSprime, ?_⟩
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn' a (fun g => ?_)
  change (TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hC
      (M : Subgroup (J : Subgroup G)) M.isClosed g)).toMulEquiv = 1
  apply MulEquiv.ext
  intro b
  apply t.injective
  have htriv : ρ (π (j g)) = 1 := hSker (q g).property
  change residualAbelianizationQuotientConjugation hC
    (N : Subgroup (H : Subgroup G)) N.isClosed
    (QuotientGroup.mk' (N : Subgroup (H : Subgroup G)) (j g)) = 1 at htriv
  rw [residualAbelianizationQuotientConjugation_mk] at htriv
  have hfixed : TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv hC
        (N : Subgroup (H : Subgroup G)) N.isClosed (j g)) (t b) = t b :=
    DFunLike.congr_fun htriv (t b)
  refine Eq.trans ?_ hfixed
  refine Quotient.inductionOn' b (fun z => ?_)
  refine Quotient.inductionOn' z (fun m => ?_)
  apply congrArg (fun n : ↥(N : Subgroup (H : Subgroup G)) =>
    TopologicalAbelianization.mk
      (↥(N : Subgroup (H : Subgroup G)) ⧸
        proCResidualCore C ↥(N : Subgroup (H : Subgroup G)))
      (QuotientGroup.mk' (proCResidualCore C ↥(N : Subgroup (H : Subgroup G))) n))
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Sigma-abelianization-faithfulness can be tested on open layers whose
relative quotient has prime order. The prime need not belong to Sigma. -/
theorem isSigmaAbFaithful_iff_prime_order_test
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    IsSigmaAbFaithful sigma G ↔
      ∀ H : OpenSubgroup G,
        letI : CompactSpace (H : Subgroup G) :=
          H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
        ∀ N : OpenNormalSubgroup (H : Subgroup G),
          Nat.Prime (Nat.card ((H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G)))) →
          residualAbelianizationQuotientConjugation
            (FiniteGroupClass.sigmaGroup_fullFormation sigma)
            (N : Subgroup (H : Subgroup G)) N.isClosed ≠ 1 := by
  constructor
  · intro hG H
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    intro N hprime
    exact (injective_iff_ne_one_of_prime_card
      (residualAbelianizationQuotientConjugation
        (FiniteGroupClass.sigmaGroup_fullFormation sigma)
        (N : Subgroup (H : Subgroup G)) N.isClosed) hprime).1 (hG H N)
  · intro htest H
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    intro N
    by_contra hnoninjective
    obtain ⟨J, M, hprime, htriv⟩ :=
      exists_prime_quotient_trivial_residual_action_of_not_injective
        (FiniteGroupClass.sigmaGroup_fullFormation sigma) H N hnoninjective
    exact htest J M hprime htriv

end ProCGroups.FiniteStepSolvableQuotients
