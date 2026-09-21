import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.ElementaryFaithfulEmbeddingSolution
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.RegularWreathKernel
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaEmbeddingSolutions
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import ProCGroups.FreeProC.Characterization.AbelianKernelOpenSubgroup
import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Data.Set.Insert

set_option autoImplicit false

/-!
# Split abelian-kernel criteria for Sigma-abelianization-faithfulness

The elementary solver passes to each open subgroup by the induced-kernel
construction. Applied to the actual regular wreath product, it produces
a proper solution with faithful kernel action for each finite quotient.
No restriction is imposed on either whole endpoint of an embedding problem.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FreeProC.Characterization

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Proper solvability of all finite split elementary `q`-kernel problems
implies `q`-abelianization-faithfulness, including all open subgroups. -/
theorem isSigmaAbFaithful_singleton_of_elementarySplit_solutions
    (q : ℕ) [Fact q.Prime]
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    IsSigmaAbFaithful {q} G := by
  apply HasFiniteFaithfulAbelianSigmaEmbeddingSolutions.isSigmaAbFaithful
  intro H B hBfinite hBdiscrete π hπ
  have : Finite B := hBfinite
  have : DiscreteTopology B := hBdiscrete
  have hH : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) (H : Subgroup G) :=
    hsolve.openSubgroup (FiniteGroupClass.abelianExponent_subgroupClosed q)
      (FiniteGroupClass.abelianExponent_finiteProductClosed q) H
  exact exists_faithful_primeKernel_embedding_solution q hH B π hπ

/-- For a nonempty set of primes, elementary split solvability at every
member gives both the Sigma condition and each singleton condition. -/
theorem isSigmaAbFaithful_of_elementarySplit_solutions
    {sigma : Set ℕ} (hne : sigma.Nonempty)
    (hprime : ∀ q ∈ sigma, Nat.Prime q)
    (hsolve : ∀ q ∈ sigma, HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    IsSigmaAbFaithful sigma G ∧ ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
  have hsingleton : ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
    intro q hq
    have : Fact q.Prime := ⟨hprime q hq⟩
    exact isSigmaAbFaithful_singleton_of_elementarySplit_solutions q (hsolve q hq)
  obtain ⟨q, hq⟩ := hne
  exact ⟨IsSigmaAbFaithful.mono (Set.singleton_subset_iff.mpr hq) (hsingleton q hq),
    hsingleton⟩

/-- Proper solvability for every finite split abelian Sigma-kernel problem
supplies all the elementary solvers required by the preceding criterion. -/
theorem isSigmaAbFaithful_of_abelianSigmaSplit_solutions
    {sigma : Set ℕ} (hne : sigma.Nonempty)
    (hprime : ∀ q ∈ sigma, Nat.Prime q)
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.sigmaGroup sigma) G) :
    IsSigmaAbFaithful sigma G ∧ ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
  apply isSigmaAbFaithful_of_elementarySplit_solutions hne hprime
  intro q hq
  have : Fact q.Prime := ⟨hprime q hq⟩
  intro P hAfin hAdisc hBfin hBdisc hsplit hker hcomm
  exact hsolve P hAfin hAdisc hBfin hBdisc hsplit
    (FiniteGroupClass.sigmaGroup_of_abelianExponent q hq hker) hcomm

end ProCGroups.FiniteStepSolvableQuotients
