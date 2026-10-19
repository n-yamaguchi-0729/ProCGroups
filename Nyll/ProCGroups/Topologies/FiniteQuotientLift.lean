/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Continuous maps assembled from finite quotients

A compatible family of continuous homomorphisms to all finite quotients of
a profinite group defines a continuous homomorphism to that group. If every
finite coordinate is surjective, the assembled homomorphism has dense range.
-/

noncomputable section

namespace ProCGroups

open CategoryTheory

universe u v

variable (P : ProfiniteGrp.{u}) {A : Type v} [Group A] [TopologicalSpace A]
    (f : ∀ N : OpenNormalSubgroup P, A →ₜ* (P.diagram.obj N : Type u))
    (hf : ∀ {N M : OpenNormalSubgroup P} (h : N ≤ M) (a : A),
      P.diagram.map h.hom (f N a) = f M a)

/-- Compatible finite coordinates define a continuous homomorphism to their inverse limit. -/
def finiteQuotientLimitMap : A →ₜ* (ProfiniteGrp.limit P.diagram : Type u) where
  toFun a := ⟨fun N => f N a, fun _ _ i => hf (leOfHom i) a⟩
  map_one' := by
    apply Subtype.ext
    funext N
    exact (f N).map_one
  map_mul' a b := by
    apply Subtype.ext
    funext N
    exact (f N).map_mul a b
  continuous_toFun := continuous_induced_rng.mpr (continuous_pi (fun N => (f N).continuous))

/-- Lift a compatible family of finite quotient coordinates to the profinite group. -/
def liftFiniteQuotients : A →ₜ* P :=
  ((ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P).symm :
    (ProfiniteGrp.limit P.diagram : Type u) →ₜ* P).comp (finiteQuotientLimitMap P f hf)

/-- Projection of the lift recovers each of its prescribed finite coordinates. -/
theorem liftFiniteQuotients_projection (N : OpenNormalSubgroup P) (a : A) :
    (QuotientGroup.mk (liftFiniteQuotients P f hf a) : P ⧸ N.toSubgroup) = f N a := by
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  exact congrArg (fun z : ProfiniteGrp.limit P.diagram => z.1 N)
    (e.apply_symm_apply (finiteQuotientLimitMap P f hf a))

/-- The lift is trivial precisely when all finite coordinates are trivial. -/
theorem liftFiniteQuotients_eq_one_iff (a : A) :
    liftFiniteQuotients P f hf a = 1 ↔ ∀ N, f N a = 1 := by
  constructor
  · intro h N
    rw [← liftFiniteQuotients_projection P f hf N a, h, QuotientGroup.mk_one]
    rfl
  · intro h
    apply ProfiniteGrp.toLimit_injective P
    apply Subtype.ext
    funext N
    change (QuotientGroup.mk (liftFiniteQuotients P f hf a) : P ⧸ N.toSubgroup) =
      QuotientGroup.mk (1 : P)
    rw [liftFiniteQuotients_projection, QuotientGroup.mk_one]
    exact h N

/-- Surjective finite coordinates give a dense inverse-limit image. -/
theorem finiteQuotientLimitMap_denseRange (hsurj : ∀ N, Function.Surjective (f N)) :
    DenseRange (finiteQuotientLimitMap P f hf) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, hx⟩
  rw [← hsv] at hx
  obtain ⟨J, fJ, hJ1, hJ2⟩ := (isOpen_pi_iff.mp hsO) _ hx
  let M := iInf (fun j : J => j.1.toSubgroup)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => j.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  obtain ⟨a, ha⟩ := hsurj m (spc m)
  refine ⟨finiteQuotientLimitMap P f hf a, ?_, a, rfl⟩
  rw [← hsv]
  apply hJ2
  intro N hN
  let i : m ⟶ N := (iInf_le (fun j : J => j.1.toSubgroup) ⟨N, hN⟩).hom
  rw [← (finiteQuotientLimitMap P f hf a).property i]
  change P.diagram.map i (f m a) ∈ _
  rw [ha]
  exact Set.mem_of_eq_of_mem (hspc i) (hJ1 N hN).2

/-- Surjective finite coordinates give a dense homomorphism to the profinite group. -/
theorem liftFiniteQuotients_denseRange (hsurj : ∀ N, Function.Surjective (f N)) :
    DenseRange (liftFiniteQuotients P f hf) :=
  (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P).symm.surjective.denseRange.comp
    (finiteQuotientLimitMap_denseRange P f hf hsurj)
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P).symm.continuous

end ProCGroups
