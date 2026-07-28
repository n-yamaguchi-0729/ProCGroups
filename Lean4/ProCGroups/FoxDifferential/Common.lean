import ProCGroups.FoxDifferential.Common.CrossedDifferential
import ProCGroups.FoxDifferential.Common.CrossedDifferentialModule
import ProCGroups.FoxDifferential.Common.FiniteFamilyLinearMap
import ProCGroups.FoxDifferential.Common.FoxBoundary
import ProCGroups.FoxDifferential.Common.FreeCrossedDifferential
import ProCGroups.FoxDifferential.Common.Jacobian

/-!
# Common Fox-differential interface

This aggregate collects the algebraic interface shared by the discrete and completed theories:
bundled crossed homomorphisms, their universal differential modules, Fox boundary identities,
free-source differentials, finite-family linear maps, and Jacobian constructions.  It does not
choose a completion topology or a finite-stage coefficient system.
-/
