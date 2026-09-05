import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.All
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.All
import ProCGroups.CompletedGroupAlgebra.Augmentation.All
import ProCGroups.CompletedGroupAlgebra.Basic.All
import ProCGroups.CompletedGroupAlgebra.FunctorialityComposition
import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.All
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.All
import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.All
import ProCGroups.CompletedGroupAlgebra.Separation
import ProCGroups.CompletedGroupAlgebra.UniversalProperty.All

set_option autoImplicit false

/-!
# Completed group algebras

Completed group algebras are constructed as inverse limits of finite-quotient group algebras.
The library develops their additive, ring, and topological structures together with projections,
augmentation maps and ideals, finite-stage functoriality, separation, and universal properties for
profinite modules.

The completed carriers are opaque; their compatible-family inverse limits are implementation
models exposed through canonical projections, extensionality, and representation equivalences.
`CanonicalCompletedGroupAlgebraModel` is the specification-level API: its inverse-limit universal
property determines comparison, continuity, density, and uniqueness rather than storing parallel
certificates.

This file is the public aggregate for every maintained `CompletedGroupAlgebra` component.
-/
