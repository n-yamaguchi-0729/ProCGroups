import ProCGroups.ProP.Fox.ClosedSpan
import ProCGroups.ProP.Fox.CoefficientReduction
import ProCGroups.ProP.Fox.CoefficientReductionCompatibility
import ProCGroups.ProP.Fox.CompletedFiltration
import ProCGroups.ProP.Fox.CompletedLeibniz
import ProCGroups.ProP.Fox.CompletedOperator
import ProCGroups.ProP.Fox.CompletedOperatorCompatibility
import ProCGroups.ProP.Fox.Derivative
import ProCGroups.ProP.Fox.FiltrationDrop
import ProCGroups.ProP.Fox.ModPBoundary
import ProCGroups.ProP.Fox.ModPDensityExactness
import ProCGroups.ProP.Fox.ModPDisplayedSpan
import ProCGroups.ProP.Fox.ModPFilteredExactness
import ProCGroups.ProP.Fox.ModPFilteredLifting
import ProCGroups.ProP.Fox.ModPFiniteStage
import ProCGroups.ProP.Fox.ModPGroupDerivative
import ProCGroups.ProP.Fox.ModPStageProjection
import ProCGroups.ProP.Fox.ModPTailExactness
import ProCGroups.ProP.Fox.Rows

set_option autoImplicit false

/-!
# Filtered Fox calculus for pro-p presentations

Reader-facing facade for completed Fox rows and their filtration.
-/


/-!
# Filtered Fox aggregate

Imports every maintained completed and filtered Fox leaf.
-/
