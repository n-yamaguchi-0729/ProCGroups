/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FoxDifferential.Completed.Continuous.Automorphism
import ProCGroups.FoxDifferential.Completed.Continuous.ChainRule.All
import ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.All
import ProCGroups.FoxDifferential.Completed.Continuous.Free.All
import ProCGroups.FoxDifferential.Completed.Continuous.Magnus.All
import ProCGroups.FoxDifferential.Completed.Continuous.Naturality
import ProCGroups.FoxDifferential.Completed.Continuous.PresentedCoordinates
import ProCGroups.FoxDifferential.Completed.Continuous.SemidirectKernelBasis
import ProCGroups.FoxDifferential.Completed.Continuous.TailExactness
import ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration
import ProCGroups.FoxDifferential.Completed.Continuous.Topology
import ProCGroups.FoxDifferential.Completed.Continuous.Universal.All

set_option autoImplicit false

/-!
# Continuous completed Fox calculus

This aggregate imports the topology and continuity of completed Fox coordinates, their naturality
and chain rules, free-source and universal constructions, topological-generation formulas,
semidirect-kernel bases, automorphism formulas, and the resulting tail exactness theorems.  The
common algebraic `CrossedHom` interface is supplied by `FoxDifferential.Common`; finite-stage and
completion-specific implementations are collected here.
-/
