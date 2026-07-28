import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Topology

/-!
# Completed Group Algebra / Basic / Within a Class

This is the public aggregate for the completion indexed by a finite-group class \(C\). It exports
the in-class quotient indices and stages, their inverse system, the opaque named carrier, its
coefficient algebra, canonical bundled projections, and the inherited inverse-limit topology.

The API deliberately mirrors the all-finite aggregate: use
`completedGroupAlgebraProjectionInClass`, `completedGroupAlgebraInClass_ext`, and
`completedGroupAlgebraInClassCompatibleFamilyEquiv` instead of constructing or projecting the
compatible-family subtype directly.
-/
