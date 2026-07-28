import ProCGroups.Abelian
import ProCGroups.Categorical
import ProCGroups.Completion
import ProCGroups.Duality
import ProCGroups.FiniteGeneration
import ProCGroups.FiniteGroups
import ProCGroups.FiniteStepSolvableQuotients
import ProCGroups.Frattini
import ProCGroups.FreeConstructions
import ProCGroups.FreeProC
import ProCGroups.FreeProducts
import ProCGroups.Generation
import ProCGroups.GroupTheory
import ProCGroups.InverseSystems
import ProCGroups.LocalWeight
import ProCGroups.NormalSubgroups
import ProCGroups.Order
import ProCGroups.Presentations
import ProCGroups.ProC
import ProCGroups.Profinite
import ProCGroups.Topologies
import ProCGroups.WreathProducts
import ProCGroups.ReidemeisterSchreier
import ProCGroups.CompletedGroupAlgebra
import ProCGroups.FoxDifferential
import ProCGroups.CrowellExactSequence

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
