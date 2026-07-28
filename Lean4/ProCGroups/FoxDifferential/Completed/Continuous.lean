import ProCGroups.FoxDifferential.Completed.Continuous.Automorphism
import ProCGroups.FoxDifferential.Completed.Continuous.ChainRule
import ProCGroups.FoxDifferential.Completed.Continuous.Free
import ProCGroups.FoxDifferential.Completed.Continuous.Naturality
import ProCGroups.FoxDifferential.Completed.Continuous.SemidirectKernelBasis
import ProCGroups.FoxDifferential.Completed.Continuous.TailExactness
import ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration
import ProCGroups.FoxDifferential.Completed.Continuous.Topology
import ProCGroups.FoxDifferential.Completed.Continuous.Universal
import ProCGroups.FoxDifferential.Completed.Continuous.PresentedCoordinates
import ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates
import ProCGroups.FoxDifferential.Completed.Continuous.Magnus

/-!
# Continuous completed Fox calculus

This aggregate imports the topology and continuity of completed Fox coordinates, their naturality
and chain rules, free-source and universal constructions, topological-generation formulas,
semidirect-kernel bases, automorphism formulas, and the resulting tail exactness theorems.  The
common algebraic `CrossedHom` interface is supplied by `FoxDifferential.Common`; finite-stage and
completion-specific implementations are collected here.
-/
