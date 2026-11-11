/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Automorphism
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ChainRule.All
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.All
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Free.All
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Magnus.All
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Naturality
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.PresentedCoordinates
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.SemidirectKernelBasis
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.TailExactness
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Topology
public import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Universal.All

/-!
# Continuous completed Fox calculus

This aggregate imports the topology and continuity of completed Fox coordinates, their naturality
and chain rules, free-source and universal constructions, topological-generation formulas,
semidirect-kernel bases, automorphism formulas, and the resulting tail exactness theorems.  The
common algebraic `CrossedHom` interface is supplied by `FoxDifferential.Common`; finite-stage and
completion-specific implementations are collected here.
-/
