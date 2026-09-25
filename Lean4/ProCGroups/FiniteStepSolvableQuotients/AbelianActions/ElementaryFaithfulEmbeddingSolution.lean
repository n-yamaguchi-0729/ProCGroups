/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.RegularWreathKernel
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.FaithfulKernel
import ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import ProCGroups.FreeProC.Characterization.EmbeddingProblems
import ProCGroups.WreathProducts
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

/-!
# Faithful prime-kernel solutions from elementary split solvability

For each actual finite quotient, apply the elementary-kernel solver to the
regular wreath product with cyclic coefficient group of order `q`. Its
right projection and canonical section give the split problem, while its
actual kernel has the faithful conjugation action constructed previously.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FreeProC.Characterization ProCGroups.WreathProducts

universe u

/-- An elementary-kernel solver produces a suitable finite extension with
faithful abelian singleton-Sigma kernel for every actual finite quotient. -/
theorem exists_faithful_primeKernel_embedding_solution
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (q : ℕ) [Fact q.Prime]
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) H)
    (B : TopGrp.{u}) [Finite B] [DiscreteTopology B]
    (π : H →ₜ* B) (hπ : Function.Surjective π) :
    ∃ E : TopGrp.{u}, Finite E ∧ DiscreteTopology E ∧
      ∃ α : E →ₜ* B, ∃ hα : Function.Surjective α,
        ∃ hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E),
          FiniteGroupClass.sigmaGroup {q} α.toMonoidHom.ker ∧
            Function.Injective (abelianKernelConjugation α.toMonoidHom hα hcomm) ∧
              Nonempty (⟨E, B, α, hα, π, hπ⟩ : TopologicalEmbeddingProblem H).ProperSolution := by
  let A := ULift.{u} (Multiplicative (ZMod q))
  let W := PermutationalWreathProduct A B B
  let : TopologicalSpace W := ⊥
  have : DiscreteTopology W := ⟨rfl⟩
  have : Finite W := Finite.of_equiv ((B → A) × B)
    (show (B → A) × B ≃ W from SemidirectProduct.equivProd.symm)
  let E : TopGrp.{u} := TopGrp.of W
  let α : E →ₜ* B :=
    { toMonoidHom := (SemidirectProduct.rightHom : W →* B)
      continuous_toFun := continuous_of_discreteTopology }
  have hα : Function.Surjective α := SemidirectProduct.rightHom_surjective
  let s : B →ₜ* E :=
    { toMonoidHom := (SemidirectProduct.inr : B →* W)
      continuous_toFun := continuous_of_discreteTopology }
  have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E) :=
    regularWreathKernel_commute (A := A) (B := B)
  have hker : FiniteGroupClass.abelianExponent q α.toMonoidHom.ker :=
    regularWreathKernel_cyclicZMod_mem_abelianExponent (B := B) q
  have hSigma : FiniteGroupClass.sigmaGroup {q} α.toMonoidHom.ker :=
    FiniteGroupClass.sigmaGroup_of_abelianExponent q (Set.mem_singleton q) hker
  have hfaithful : Function.Injective
      (abelianKernelConjugation α.toMonoidHom hα hcomm) :=
    regularWreathKernel_conjugation_injective (A := A) (B := B)
  let P : TopologicalEmbeddingProblem H := ⟨E, B, α, hα, π, hπ⟩
  have hsplit : P.IsSplit := by
    refine ⟨s, ?_⟩
    apply ContinuousMonoidHom.ext
    intro b
    change (SemidirectProduct.rightHom : W →* B)
      ((SemidirectProduct.inr : B →* W) b) = b
    exact SemidirectProduct.rightHom_inr b
  have hproper : Nonempty P.ProperSolution :=
    hsolve P inferInstance inferInstance inferInstance inferInstance hsplit hker hcomm
  exact ⟨E, inferInstance, inferInstance, α, hα, hcomm, hSigma, hfaithful, hproper⟩

end ProCGroups.FiniteStepSolvableQuotients
