import ProCGroups.Abelian.All
import ProCGroups.Boundary.All
import ProCGroups.Categorical.All
import ProCGroups.Cohomology.All
import ProCGroups.CompletedGroupAlgebra.All
import ProCGroups.Completion.All
import ProCGroups.CrowellExactSequence.All
import ProCGroups.Duality
import ProCGroups.FiniteGeneration.All
import ProCGroups.FiniteGroups.All
import ProCGroups.FiniteStepSolvableQuotients.All
import ProCGroups.FoxDifferential.All
import ProCGroups.Frattini
import ProCGroups.FreeConstructions.All
import ProCGroups.FreeProC.All
import ProCGroups.FreeProducts.All
import ProCGroups.Generation.All
import ProCGroups.GolodShafarevich.All
import ProCGroups.GroupTheory.All
import ProCGroups.InverseSystems.All
import ProCGroups.LocalWeight.All
import ProCGroups.NormalSubgroups.All
import ProCGroups.Order.All
import ProCGroups.Presentations.All
import ProCGroups.ProC.All
import ProCGroups.ProP.All
import ProCGroups.Profinite.All
import ProCGroups.ReidemeisterSchreier.All
import ProCGroups.TopologicalGroups
import ProCGroups.Topologies.All
import ProCGroups.WreathProducts

set_option autoImplicit false

/-!
# Pro-C groups

Reusable formalization of profinite and pro-\(C\) groups.  The library covers finite-group
classes, inverse systems and completions, free pro-\(C\) groups and products, generation,
presentations, duality, topologies, and wreath products.

`ProCGrp C` is the full subcategory of `ProfiniteGrp` cut out by the open-normal finite-quotient
basis condition for `C`; its categorical and concrete structures are inherited from Mathlib.
`FiniteGroupClass` includes finiteness and invariance under multiplicative equivalence, so the
corresponding finite-group object property is isomorphism-invariant without extra hypotheses.

This public aggregate imports every maintained Pro-C Groups component, including the
Reidemeister--Schreier, completed group algebra, Fox differential, and Crowell exact-sequence
layers.
-/
