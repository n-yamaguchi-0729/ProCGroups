/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Abelianization faithfulness

For every open subgroup `H` and every open normal subgroup `N` of `H`,
the quotient `H/N` acts faithfully on the topological abelianization of `N`.
The relative pro-Σ version uses the same quotient-conjugation action on
the maximal pro-Σ quotient.
-/

@[expose] public section

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

/-- For every open subgroup `H` and open normal subgroup `N` of `H`,
the quotient `H/N` acts faithfully on the topological abelianization of `N`. -/
def IsAbFaithful
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : Prop :=
  ∀ H : OpenSubgroup G,
    ∀ N : OpenNormalSubgroup ↥(H : Subgroup G),
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G))))

/-- Definition in Section 1: every finite relative quotient acts faithfully
on the abelianized maximal pro-`Σ` quotient of its open normal subgroup. -/
def IsSigmaAbFaithful (sigma : Set ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ∀ H : OpenSubgroup G,
    letI : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    ∀ N : OpenNormalSubgroup (H : Subgroup G),
      Function.Injective
        (residualAbelianizationQuotientConjugation
          (FiniteGroupClass.sigmaGroup_fullFormation sigma)
          (N : Subgroup (H : Subgroup G)) N.isClosed)

end ProCGroups.FiniteStepSolvableQuotients
