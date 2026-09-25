/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaEmbeddingSolutions
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SigmaFaithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.ResidualSelfCentralizingQuotient
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.FaithfulKernel
import ProCGroups.FreeProC.Characterization.EmbeddingProblems
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.Topologies.QuotientMaps
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# The finite embedding formulation of Sigma-abelianization-faithfulness

The actual finite ambient quotient constructed from a faithful residual
abelian quotient supplies the extension and its proper solution. Its kernel
is exactly the image of the original normal subgroup, so it is a Sigma group.
No Sigma restriction is placed on the original finite quotient.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FreeProC.Characterization

universe u

/-- Sigma-abelianization-faithfulness constructs a suitable finite extension
with faithful abelian Sigma kernel and a proper solution for each quotient. -/
theorem IsSigmaAbFaithful.hasFiniteFaithfulAbelianSigmaEmbeddingSolutions
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsSigmaAbFaithful sigma G) :
    HasFiniteFaithfulAbelianSigmaEmbeddingSolutions sigma G := by
  intro H B hBfinite hBdiscrete π hπ
  have : DiscreteTopology B := hBdiscrete
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let N : OpenNormalSubgroup (H : Subgroup G) := ProC.OpenNormalSubgroup.ker π
  obtain ⟨R, hRN, hImage, hcommR, hcentralizerR⟩ :=
    exists_openNormal_abelian_selfCentralizing_quotient_inClass
      (FiniteGroupClass.sigmaGroup_fullFormation sigma) N (hG H N)
  let E : TopGrp.{u} := TopGrp.of ((H : Subgroup G) ⧸ (R : Subgroup (H : Subgroup G)))
  let α : E →ₜ* B := QuotientGroup.liftₜ (R : Subgroup (H : Subgroup G)) π hRN
  have hαmk (h : (H : Subgroup G)) :
      α (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) h) = π h := rfl
  have hα : Function.Surjective α := by
    intro b
    obtain ⟨h, rfl⟩ := hπ b
    exact ⟨QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) h, hαmk h⟩
  let ψ : (N : Subgroup (H : Subgroup G)) →* E :=
    (ProC.OpenNormalSubgroup.quotientProj R).toMonoidHom.comp
      (N : Subgroup (H : Subgroup G)).subtype
  have hRange : ψ.range = α.toMonoidHom.ker := by
    ext e
    constructor
    · intro he
      obtain ⟨n, rfl⟩ := he
      change α (QuotientGroup.mk' (R : Subgroup (H : Subgroup G))
        (n : (H : Subgroup G))) = 1
      rw [hαmk]
      exact n.property
    · intro he
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) e
      have hn : h ∈ N := by
        change π h = 1
        rw [← hαmk]
        exact he
      exact ⟨⟨h, hn⟩, rfl⟩
  have hSigma : FiniteGroupClass.sigmaGroup sigma α.toMonoidHom.ker :=
    hRange ▸ hImage
  have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E) := by
    intro a b
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) (a : E)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) (b : E)
    have hxN : x ∈ N := by
      change π x = 1
      rw [← hαmk, hx]
      exact a.property
    have hyN : y ∈ N := by
      change π y = 1
      rw [← hαmk, hy]
      exact b.property
    rw [← hx, ← hy]
    exact hcommR ⟨x, hxN⟩ ⟨y, hyN⟩
  have hfaithful : Function.Injective (abelianKernelConjugation α.toMonoidHom hα hcomm) := by
    apply (abelianKernelConjugation_injective_iff α.toMonoidHom hα hcomm).mpr
    intro e he
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) e
    change π h = 1
    apply hcentralizerR h
    intro n
    apply he ⟨QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) (n : (H : Subgroup G)), ?_⟩
    change π (n : (H : Subgroup G)) = 1
    exact n.property
  refine ⟨E, inferInstance, inferInstance, α, hα, hcomm, hSigma, hfaithful, ?_⟩
  exact ⟨⟨ProC.OpenNormalSubgroup.quotientProj R,
    ProC.OpenNormalSubgroup.quotientProj_surjective R, rfl⟩⟩

/-- The paper's finite abelian Sigma-kernel embedding formulation, with
proper solutions and a separately chosen extension for each finite quotient. -/
theorem isSigmaAbFaithful_iff_hasFiniteFaithfulAbelianSigmaEmbeddingSolutions
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    IsSigmaAbFaithful sigma G ↔ HasFiniteFaithfulAbelianSigmaEmbeddingSolutions sigma G :=
  ⟨IsSigmaAbFaithful.hasFiniteFaithfulAbelianSigmaEmbeddingSolutions,
    HasFiniteFaithfulAbelianSigmaEmbeddingSolutions.isSigmaAbFaithful⟩

end ProCGroups.FiniteStepSolvableQuotients
