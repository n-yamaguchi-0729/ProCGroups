import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.CanonicalMap

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Limit

This aggregate exports the two-parameter inverse limit
\(\varprojlim_{I,U}(R/I)[G/U]\), its opaque named carrier, canonical bundled quotient
projections, inherited topological-ring structure, and the dense canonical map from \(R[G]\).

The carrier's compatible-family realization is available only through
`completedGroupAlgebraOpenFiniteQuotientCompatibleFamilyEquiv`; ordinary consumers should use
`completedGroupAlgebraOpenFiniteQuotientLimitProjection` and
`completedGroupAlgebraOpenFiniteQuotientLimit_ext`.
-/
