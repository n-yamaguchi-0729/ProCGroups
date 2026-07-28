import ProCGroups.CompletedGroupAlgebra.Basic
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality
import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality
import ProCGroups.CompletedGroupAlgebra.Augmentation
import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation
import ProCGroups.CompletedGroupAlgebra.UniversalProperty
import ProCGroups.CompletedGroupAlgebra.FunctorialityComposition
import ProCGroups.CompletedGroupAlgebra.Separation
import ProCGroups.CompletedGroupAlgebra.ProfiniteModules

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
