import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteGroups.SigmaMonotonicity
import ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationMonotonicity
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Sigma-abelianization-faithfulness

The quantifiers range over all open subgroups and all their open normal
subgroups, without restricting the prime divisors of the relative index.
The action is the existing conjugation action on the actual residual quotient.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC

universe u

/-- Every finite relative quotient acts faithfully on the abelianized maximal
pro-Sigma quotient of its open normal subgroup. -/
def IsSigmaAbFaithful (sigma : Set ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ∀ H : OpenSubgroup G,
    letI : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    ∀ N : OpenNormalSubgroup (H : Subgroup G),
      Function.Injective
        (residualAbelianizationQuotientConjugation
          (FiniteGroupClass.sigmaGroup_fullFormation sigma)
          (N : Subgroup (H : Subgroup G)) N.isClosed)

/-- Enlarging the permitted set of primes preserves Sigma-abelianization-faithfulness. -/
theorem IsSigmaAbFaithful.mono {sigma tau : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h : sigma ⊆ tau) (hG : IsSigmaAbFaithful sigma G) :
    IsSigmaAbFaithful tau G := by
  intro H
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N
  exact residualAbelianizationQuotientConjugation_injective_of_class_inclusion
    (FiniteGroupClass.sigmaGroup_fullFormation sigma)
    (FiniteGroupClass.sigmaGroup_fullFormation tau)
    (fun {Q : Type u} [Group Q] hQ => FiniteGroupClass.sigmaGroup_mono h hQ)
    (N : Subgroup (H : Subgroup G)) N.isClosed (hG H N)

end ProCGroups.FiniteStepSolvableQuotients
