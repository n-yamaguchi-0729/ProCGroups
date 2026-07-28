import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Topology

/-!
# Completed Group Algebra / Basic / All Finite

This is the public aggregate for the all-finite completion \(\widehat{R[G]}\). It exports:

* finite-quotient indices, stages, and transition maps;
* the opaque named carrier and its explicit compatible-family equivalence;
* the generic inverse-limit ring, module, and coefficient-algebra structures;
* canonical bundled finite-stage projections and their linear, algebra, and continuous forms; and
* the inverse-limit topological-ring, compactness, Hausdorff, and disconnectedness results.

Downstream code should use `completedGroupAlgebraProjection`, `completedGroupAlgebra_ext`, and
`completedGroupAlgebraCompatibleFamilyEquiv`; the concrete compatible-family subtype is not a
second public carrier.
-/
