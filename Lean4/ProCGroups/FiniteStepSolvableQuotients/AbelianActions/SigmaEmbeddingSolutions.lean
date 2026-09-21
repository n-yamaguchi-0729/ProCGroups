import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.ResidualSelfCentralizingImage
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.FaithfulKernel
import ProCGroups.FreeProC.Characterization.EmbeddingProblems
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteGroups.Classes
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Proper finite embedding solutions with faithful abelian Sigma kernels

For each finite quotient, the extension with finite abelian Sigma kernel may
be chosen separately. A proper solution is surjective. Its image of the
original kernel lies in the Sigma kernel, so the actual residual quotient
and its abelianization detect the finite faithful action.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FreeProC.Characterization

universe u

/-- Each finite quotient of each open subgroup admits a suitable finite
extension with faithful abelian Sigma kernel and a proper solution. -/
def HasFiniteFaithfulAbelianSigmaEmbeddingSolutions
    (sigma : Set ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ H : OpenSubgroup G, ∀ B : TopGrp.{u},
    Finite B → DiscreteTopology B →
      ∀ π : (H : Subgroup G) →ₜ* B, ∀ hπ : Function.Surjective π,
        ∃ E : TopGrp.{u}, Finite E ∧ DiscreteTopology E ∧
          ∃ α : E →ₜ* B, ∃ hα : Function.Surjective α,
            ∃ hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E),
              FiniteGroupClass.sigmaGroup sigma α.toMonoidHom.ker ∧
                Function.Injective (abelianKernelConjugation α.toMonoidHom hα hcomm) ∧
                  Nonempty (⟨E, B, α, hα, π, hπ⟩ :
                    TopologicalEmbeddingProblem (H : Subgroup G)).ProperSolution

/-- Proper solutions with faithful abelian Sigma kernels imply the actual
Sigma-abelianization-faithfulness condition. -/
theorem HasFiniteFaithfulAbelianSigmaEmbeddingSolutions.isSigmaAbFaithful
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasFiniteFaithfulAbelianSigmaEmbeddingSolutions sigma G) :
    IsSigmaAbFaithful sigma G := by
  intro H
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N
  let B : TopGrp.{u} := TopGrp.of ((H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G)))
  obtain ⟨E, hEfinite, hEdiscrete, α, hα, hcomm, hSigma, hfaithful, ⟨θ⟩⟩ :=
    hG H B inferInstance inferInstance (ProC.OpenNormalSubgroup.quotientProj N)
      (ProC.OpenNormalSubgroup.quotientProj_surjective N)
  have : DiscreteTopology E := hEdiscrete
  have hsquare (h : (H : Subgroup G)) :
      α (θ.val h) = ProC.OpenNormalSubgroup.quotientProj N h :=
    DFunLike.congr_fun θ.property.2 h
  have hθN (n : (N : Subgroup (H : Subgroup G))) :
      θ.val (n : (H : Subgroup G)) ∈ α.toMonoidHom.ker := by
    change α (θ.val (n : (H : Subgroup G))) = 1
    rw [hsquare]
    exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mpr n.property
  let f : (N : Subgroup (H : Subgroup G)) →* E :=
    θ.val.toMonoidHom.comp (N : Subgroup (H : Subgroup G)).subtype
  let i : f.range →* α.toMonoidHom.ker :=
    { toFun := fun a => ⟨a.val, by
        obtain ⟨n, hn⟩ := a.property
        rw [← hn]
        exact hθN n⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hImage : FiniteGroupClass.sigmaGroup sigma f.range :=
    (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary.of_injective hSigma i
      (fun a b hab => Subtype.ext
        (congrArg (fun z : α.toMonoidHom.ker => (z : E)) hab))
  apply injective_residualQuotientConjugation_of_selfCentralizing_image
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) N θ.val hImage
  · intro n m
    exact hcomm ⟨θ.val (n : (H : Subgroup G)), hθN n⟩
      ⟨θ.val (m : (H : Subgroup G)), hθN m⟩
  · intro h hh
    have hker : θ.val h ∈ α.toMonoidHom.ker := by
      apply (abelianKernelConjugation_injective_iff α.toMonoidHom hα hcomm).mp hfaithful
      intro a
      obtain ⟨n, hn⟩ := θ.property.1 (a : E)
      have hnN : n ∈ N := by
        apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
        rw [← hsquare, hn]
        exact a.property
      rw [← hn]
      exact hh ⟨n, hnN⟩
    apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
    rw [← hsquare]
    exact hker

end ProCGroups.FiniteStepSolvableQuotients
