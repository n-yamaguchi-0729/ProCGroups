/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

/-!
# Open subgroups preserve Sigma-abelianization-faithfulness

The subgroup of an open subgroup is mapped into the ambient group by the
actual subtype inclusion. Residual conjugation is transported by the resulting
continuous group equivalence.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC

universe u

/-- Every open subgroup of a Sigma-abelianization-faithful profinite group
is Sigma-abelianization-faithful. -/
theorem IsSigmaAbFaithful.openSubgroup {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsSigmaAbFaithful sigma G) (U : OpenSubgroup G) :
    letI : CompactSpace (U : Subgroup G) :=
      U.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    IsSigmaAbFaithful sigma (U : Subgroup G) := by
  have : CompactSpace (U : Subgroup G) :=
    U.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro H
  have : CompactSpace (H : Subgroup (U : Subgroup G)) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N
  let Hmap : OpenSubgroup G :=
    { toSubgroup := (H : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype
      isOpen' := U.isOpen.isOpenMap_subtype_val _ H.isOpen }
  have : CompactSpace (Hmap : Subgroup G) :=
    Hmap.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let e : (H : Subgroup (U : Subgroup G)) ≃* (Hmap : Subgroup G) :=
    (H : Subgroup (U : Subgroup G)).equivMapOfInjective
      (U : Subgroup G).subtype Subtype.val_injective
  have he : Continuous e :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  let t : (H : Subgroup (U : Subgroup G)) ≃ₜ* (Hmap : Subgroup G) :=
    { toMulEquiv := e
      continuous_toFun := he
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap).continuous_invFun }
  let Nmap : OpenNormalSubgroup (Hmap : Subgroup G) :=
    ProCGroups.ProC.OpenNormalSubgroup.map
      (ContinuousMonoidHom.toContinuousMonoidHom t)
      t.toHomeomorph.isOpenMap t.surjective N
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) t
    (N : Subgroup (H : Subgroup (U : Subgroup G))) N.isClosed).mp (hG Hmap Nmap)

end ProCGroups.FiniteStepSolvableQuotients
