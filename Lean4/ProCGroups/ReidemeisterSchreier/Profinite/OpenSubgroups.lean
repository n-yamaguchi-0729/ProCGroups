import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisFiniteRank
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisTheorems
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.DenseFreeModel
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.ExactRightSchreierGeneration
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.FinitePermutationTargets
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.MinimalPower
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient
import ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.SchreierTransversals

/-!
# Profinite open-subgroup Reidemeister--Schreier theory

This aggregate exports the concrete right-quotient and Schreier-cocycle
constructions, exact right-Schreier generation, finite permutation targets,
rank bounds, and finite-rank basis theorems for open subgroups of
free pro-\(C\) groups.

Basis conclusions use `EpimorphicallyFreeProCGroupOnConvergingSetData` directly.  There is no
parallel RS-specific carrier/model wrapper layer.
-/
