/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.Topology.Constructions.SumProd

/-!
# Joint continuity of quotient conjugation on topological abelianization

The existing action descends from continuous conjugation through the product
of the two open quotient maps. No new action is constructed.
-/

open ProCGroups.Abelian

namespace ProCGroups.Abelian

/-- The existing quotient-conjugation action is jointly continuous. -/
theorem continuous_quotientConjugationTopologicalAbelianizationMap
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] :
    Continuous (fun p : (G ⧸ N) × TopologicalAbelianization N =>
      quotientConjugationTopologicalAbelianizationMap N p.1 p.2) := by
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
    (QuotientGroup.isOpenQuotientMap_mk (N := Subgroup.closedCommutator N))
  apply hq.continuous_comp_iff.mp
  change Continuous (fun p : G × N =>
    quotientConjugationTopologicalAbelianizationMap N
      (QuotientGroup.mk' N p.1) (TopologicalAbelianization.mk N p.2))
  simp_rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk]
  have hc : Continuous (fun p : G × N => ((MulAut.conjNormal p.1) p.2 : G)) := by
    change Continuous (fun p : G × N => p.1 * (p.2 : G) * p.1⁻¹)
    exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul
      continuous_fst.inv
  exact (TopologicalAbelianization.mkₜ N).continuous_toFun.comp
    (hc.subtype_mk (fun p => ((MulAut.conjNormal p.1) p.2).property))

end ProCGroups.Abelian
