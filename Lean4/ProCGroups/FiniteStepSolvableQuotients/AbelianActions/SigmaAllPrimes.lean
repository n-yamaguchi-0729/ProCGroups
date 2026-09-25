/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaProGroup
import ProCGroups.ProC.InverseLimits.FiniteQuotients
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.FiniteGroups.AllFinite
import ProCGroups.FiniteGroups.StandardClasses

set_option autoImplicit false

/-!
# The set of all primes recovers ordinary faithfulness
-/

namespace ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Allowing all primes gives exactly ordinary abelianization-faithfulness. -/
theorem isSigmaAbFaithful_univ_iff {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    IsSigmaAbFaithful Set.univ G ↔ IsAbFaithful G := by
  apply isSigmaAbFaithful_iff_isAbFaithful_of_proSigma
  apply (ProC.hasOpenNormalBasisInClass_allFinite (G := G)).mono
  intro Q _ hQ
  refine ⟨hQ, ?_⟩
  intro p _ hp
  exact False.elim (hp (Set.mem_univ p))

end ProCGroups.FiniteStepSolvableQuotients
