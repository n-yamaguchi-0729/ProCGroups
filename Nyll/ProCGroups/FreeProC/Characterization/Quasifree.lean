/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FreeProC.Characterization.EmbeddingProblems
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

/-!
# Pro C Groups / Free pro-C / Characterization / Quasifree

This module formulates quasifreeness by the exact number of proper solutions of every
nontrivial finite split embedding problem. Topological generating-set cardinality is recorded
separately; it does not replace this exact solution count.
-/

@[expose] public section

noncomputable section

open scoped Cardinal

namespace ProCGroups.FreeProC.Characterization

universe u

/-- A topological group has a topological generating set of cardinality \(\kappa\). -/
def HasTopologicalGeneratingSetOfCardinality
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (κ : Cardinal) : Prop :=
  ∃ S : Set G, Generation.TopologicallyGenerates (G := G) S ∧ Cardinal.mk S = κ

/--
Every nontrivial finite split \(C\)-embedding problem has exactly \(\kappa\) proper solutions.
The restriction to nontrivial covering maps excludes the uniquely solvable isomorphism problems.
This is the proper-solution condition of Harbater--Stevenson, *Local Galois theory in dimension
two*, Section 2, restricted to the chosen finite-group class.
-/
def HasQuasifreeProperSolutionProperty
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (κ : Cardinal) : Prop :=
  ∀ P : TopologicalEmbeddingProblem G,
    IsFiniteSplitCEmbeddingProblem C P → P.IsNontrivial →
      Cardinal.mk P.ProperSolution = κ

/--
Quasifreeness at infinite rank \(\kappa\) in the chosen finite-group class.
The ambient group is profinite and pro-\(C\), and each nontrivial finite split problem has
exactly \(\kappa\) proper solutions. The existence of a dense generating set of a specified
cardinality is a separate condition and is not used as a substitute for this rank condition.
-/
def IsQuasifreeOfRank (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (κ : Cardinal) : Prop :=
  ProCGroups.ProC.HasOpenNormalBasisInClass C G ∧
    Cardinal.aleph0 ≤ κ ∧ HasQuasifreeProperSolutionProperty C G κ

end ProCGroups.FreeProC.Characterization
