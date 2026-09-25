/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaOrdinary
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.ProC.MaximalQuotients.ResidualProGroupFaithfulness
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Sigma-faithfulness for pro-Sigma groups

Every closed subgroup of a pro-Sigma group is pro-Sigma. Its actual
residual quotient therefore retains the ordinary abelianization action.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC

universe u

/-- On a pro-Sigma group, Sigma-abelianization-faithfulness is equivalent
to ordinary abelianization-faithfulness. No nonemptiness of Sigma is needed. -/
theorem isSigmaAbFaithful_iff_isAbFaithful_of_proSigma
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G) :
    IsSigmaAbFaithful sigma G ↔ IsAbFaithful G := by
  constructor
  · exact IsSigmaAbFaithful.isAbFaithful
  · intro hfaith H
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    intro N
    have hH : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma)
        (H : Subgroup G) :=
      HasOpenNormalBasisInClass.of_isClosed_subgroup_of_fullFormation
        (FiniteGroupClass.sigmaGroup_fullFormation sigma) hpro
        (H : Subgroup G) H.isClosed
    have hN : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma)
        (N : Subgroup (H : Subgroup G)) :=
      HasOpenNormalBasisInClass.of_isClosed_subgroup_of_fullFormation
        (FiniteGroupClass.sigmaGroup_fullFormation sigma) hH
        (N : Subgroup (H : Subgroup G)) N.isClosed
    exact residualAbelianizationQuotientConjugation_injective_of_ordinary_of_proC
      (FiniteGroupClass.sigmaGroup_fullFormation sigma)
      (N : Subgroup (H : Subgroup G)) N.isClosed hN (hfaith H N)

end ProCGroups.FiniteStepSolvableQuotients
