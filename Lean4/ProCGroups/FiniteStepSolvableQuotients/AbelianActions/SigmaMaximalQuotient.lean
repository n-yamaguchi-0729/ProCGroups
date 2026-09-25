/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.ProC.MaximalQuotients.ResidualUniversalProperty
import ProCGroups.ProC.MaximalQuotients.SubgroupComparison
import ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.Profinite.OpenSubgroups
import ProCGroups.Topologies.QuotientMaps
import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.Algebra.Group.Hom.Basic

set_option autoImplicit false

/-!
# Abelianization-faithfulness of the maximal pro-Sigma quotient

Open subgroups and their open normal subgroups are pulled back along the actual
residual projection. The maximal-quotient subgroup comparison identifies the
residual quotient of each preimage with the original subgroup and preserves
conjugation. Thus Sigma-abelianization-faithfulness gives ordinary
abelianization-faithfulness of the maximal pro-Sigma quotient.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

private theorem quotient_action_injective_of_residual_preimage
    {C : FiniteGroupClass.{u}}
    {G Q : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hC : FiniteGroupClass.FullFormation C)
    (π : G →ₜ* Q) (hπ : IsMaximalProCQuotient C π.toMonoidHom)
    (N : OpenNormalSubgroup Q)
    (hfaith : Function.Injective
      (residualAbelianizationQuotientConjugation hC
        ((N : Subgroup Q).comap π.toMonoidHom)
        (N.isClosed.preimage π.continuous_toFun))) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap (N := (N : Subgroup Q))) := by
  let e := TopologicalAbelianization.congr
    (residualQuotientPreimageContinuousMulEquiv hC π hπ (N : Subgroup Q) N.isClosed)
  apply (injective_iff_map_eq_one
    (quotientConjugationTopologicalAbelianizationMap (N := (N : Subgroup Q)))).mpr
  intro a ha
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (N : Subgroup Q) a
  obtain ⟨g, rfl⟩ := hπ.surjective_π q
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup Q)) (π g)).mpr
  by_contra hg
  apply (residualAbelianizationQuotientConjugation_injective_iff hC
    ((N : Subgroup Q).comap π.toMonoidHom)
    (N.isClosed.preimage π.continuous_toFun)).mp hfaith g hg
  apply MulEquiv.ext
  intro x
  apply e.injective
  refine (residualQuotientPreimage_abelianization_conjugation hC π hπ
    (N : Subgroup Q) N.isClosed g x).trans ?_
  obtain ⟨n, hn⟩ := TopologicalAbelianization.surjective_mk (N : Subgroup Q) (e x)
  change TopologicalAbelianization.congr
    (Subgroup.conjNormalContinuousMulEquiv (N : Subgroup Q) (π g)) (e x) = e x
  rw [← hn]
  change conjugationTopologicalAbelianizationContinuousAut (N : Subgroup Q) (π g)
    (TopologicalAbelianization.mk (N : Subgroup Q) n) =
      TopologicalAbelianization.mk (N : Subgroup Q) n
  rw [conjugationTopologicalAbelianizationContinuousAut_toMulAut_apply_mk]
  exact DFunLike.congr_fun ha (TopologicalAbelianization.mk (N : Subgroup Q) n)

/-- The actual maximal pro-Sigma quotient of a Sigma-abelianization-faithful
profinite group is abelianization-faithful. -/
theorem IsSigmaAbFaithful.isAbFaithful_residualQuotient
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsSigmaAbFaithful sigma G) :
    IsAbFaithful (G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.sigmaGroup sigma
  let Q := G ⧸ proCResidualCore C G
  have hRclosed : IsClosed ((proCResidualCore C G : Subgroup G) : Set G) :=
    proCResidualCore_isClosed C G
  have : TotallyDisconnectedSpace Q :=
    totallyDisconnectedSpace_quotient_closedNormal (proCResidualCore C G) hRclosed
  let π : G →ₜ* Q :=
    ⟨QuotientGroup.mk' (proCResidualCore C G), QuotientGroup.continuous_mk⟩
  have hπ : IsMaximalProCQuotient C π.toMonoidHom :=
    isMaximalProCQuotient_residualCore (FiniteGroupClass.sigmaGroup_formation sigma)
      (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary
  intro H N
  have : CompactSpace (H : Subgroup Q) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let H' : OpenSubgroup G := H.comap π.toMonoidHom π.continuous_toFun
  have : CompactSpace (H' : Subgroup G) :=
    H'.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let πH : (H' : Subgroup G) →ₜ* (H : Subgroup Q) :=
    ContinuousMonoidHom.restrictPreimage π (H : Subgroup Q)
  have hπH : IsMaximalProCQuotient C πH.toMonoidHom :=
    hπ.restrictPreimage (FiniteGroupClass.sigmaGroup_fullFormation sigma)
      π (H : Subgroup Q)
  let N' : OpenNormalSubgroup (H' : Subgroup G) :=
    ProCGroups.OpenNormalSubgroup.comap πH.toMonoidHom πH.continuous_toFun N
  exact quotient_action_injective_of_residual_preimage
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) πH hπH N (hG H' N')

end ProCGroups.FiniteStepSolvableQuotients
