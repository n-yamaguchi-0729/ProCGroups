/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.Transfer
public import Nyll.ProCGroups.GroupTheory.MonoidHomMapTransferEqTransferComp

/-!
# Original topological transfer and finite quotient transfer

The original continuous transfer uses a normalized section of the finite
coset space. Its image is an actual left transversal. Reindexing the
defining product identifies this transfer with Mathlib's transfer.

A homomorphism which identifies the two coset spaces transports an actual
transversal. Comparing the defining products gives character-valued transfer
naturality, including the case of a surjective quotient.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian ProCGroups.ProC

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The original continuous transfer product is Mathlib's transfer into the
actual topological abelianization of the open subgroup. -/
theorem openNormalTransferPre_eq_transfer
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))] (g : G) :
    let _ : (N : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    openNormalTransferTopologicalAbelianizationPre N g =
      MonoidHom.transfer (TopologicalAbelianization.mk (N : Subgroup G)) g := by
  intro hindex
  classical
  let _ : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  let ρ : G ⧸ (N : Subgroup G) → G :=
    quotientOpenSubgroupSection (N : Subgroup G)
  have hρ : ∀ q : G ⧸ (N : Subgroup G),
      (ρ q : G ⧸ (N : Subgroup G)) = q :=
    quotientOpenSubgroupSection_rightInverse (N : Subgroup G)
  let T : (N : Subgroup G).LeftTransversal :=
    ⟨Set.range ρ, Subgroup.isComplement_range_left hρ⟩
  have hT (q : G ⧸ (N : Subgroup G)) :
      (T.property.leftQuotientEquiv q : G) = ρ q :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hρ q
  let η (q : G ⧸ (N : Subgroup G)) : (N : Subgroup G) :=
    ⟨(T.property.leftQuotientEquiv q : G)⁻¹ *
        ((g • T).property.leftQuotientEquiv q : G),
      QuotientGroup.leftRel_apply.mp (Quotient.exact'
        ((T.property.leftQuotientEquiv.symm_apply_apply q).trans
          ((g • T).property.leftQuotientEquiv.symm_apply_apply q).symm))⟩
  have haction (q : G ⧸ (N : Subgroup G)) :
      (QuotientGroup.mk g : G ⧸ (N : Subgroup G)) * q = g • q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  have hterm (q : G ⧸ (N : Subgroup G)) :
      openNormalTransferTerm N q g = η (g • q) := by
    apply Subtype.ext
    change (ρ ((QuotientGroup.mk g : G ⧸ (N : Subgroup G)) * q))⁻¹ * g * ρ q =
      (T.property.leftQuotientEquiv (g • q) : G)⁻¹ *
        ((g • T).property.leftQuotientEquiv (g • q) : G)
    rw [haction]
    simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul,
      inv_smul_smul, hT, smul_eq_mul]
    exact mul_assoc _ _ _
  rw [MonoidHom.transfer_def _ T g]
  change (∏ q : G ⧸ (N : Subgroup G),
      TopologicalAbelianization.mk (N : Subgroup G) (openNormalTransferTerm N q g)) =
    ∏ q : G ⧸ (N : Subgroup G), TopologicalAbelianization.mk (N : Subgroup G) (η q)
  calc
    (∏ q : G ⧸ (N : Subgroup G),
        TopologicalAbelianization.mk (N : Subgroup G) (openNormalTransferTerm N q g)) =
        ∏ q : G ⧸ (N : Subgroup G),
          TopologicalAbelianization.mk (N : Subgroup G) (η (g • q)) := by
      apply Finset.prod_congr rfl
      intro q _
      exact congrArg (TopologicalAbelianization.mk (N : Subgroup G)) (hterm q)
    _ = ∏ q : G ⧸ (N : Subgroup G),
        TopologicalAbelianization.mk (N : Subgroup G) (η q) :=
      Equiv.prod_comp (MulAction.toPerm g)
        (fun q => TopologicalAbelianization.mk (N : Subgroup G) (η q))

/-- Every continuous commutative character of the original topological
transfer is its ordinary group-theoretic transfer. -/
theorem lift_openNormalTransfer_apply_mk
    {A : Type*} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    (χ : (N : Subgroup G) →ₜ* A) (g : G) :
    let _ : (N : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    TopologicalAbelianization.lift χ
        (openNormalTransferTopologicalAbelianization N (TopologicalAbelianization.mk G g)) =
      MonoidHom.transfer χ.toMonoidHom g := by
  intro hindex
  change TopologicalAbelianization.lift χ
    (openNormalTransferTopologicalAbelianizationPre N g) = _
  rw [openNormalTransferPre_eq_transfer]
  change (TopologicalAbelianization.lift χ).toMonoidHom
      (MonoidHom.transfer (TopologicalAbelianization.mk (N : Subgroup G)) g) =
    MonoidHom.transfer χ.toMonoidHom g
  rw [MonoidHom.map_transfer_eq_transfer_comp]
  have hχ : (TopologicalAbelianization.lift χ).toMonoidHom.comp
      (TopologicalAbelianization.mk (N : Subgroup G)) = χ.toMonoidHom := by
    apply MonoidHom.ext
    intro n
    rfl
  rw [hχ]

end ProCGroups.FiniteStepSolvableQuotients

namespace ClassFormation

variable {P Q A : Type*} [Group P] [Group Q] [CommGroup A]

/-- Character-valued transfer commutes with a homomorphism inducing a
bijection of the left coset spaces. -/
theorem transfer_character_natural_of_coset_surjective
    (f : P →* Q) (H : Subgroup P) (J : Subgroup Q)
    (hcomap : J.comap f = H) [H.FiniteIndex] [J.FiniteIndex]
    (hquot : ∀ q : Q, ∃ p : P, (f p : Q ⧸ J) = (q : Q ⧸ J))
    (χ : J →* A) (p : P) :
    MonoidHom.transfer (χ.comp ((f.comp H.subtype).codRestrict J
      (fun x => show (x : P) ∈ J.comap f from hcomap.symm ▸ x.property))) p =
      MonoidHom.transfer χ (f p) := by
  classical
  let qf : P ⧸ H → Q ⧸ J :=
    Quotient.map' f (fun x y hxy => by
      rw [QuotientGroup.leftRel_apply, ← f.map_inv, ← f.map_mul]
      change x⁻¹ * y ∈ J.comap f
      rw [hcomap]
      exact QuotientGroup.leftRel_apply.mp hxy)
  have hqf : Function.Bijective qf := by
    constructor
    · refine Quotient.ind' (fun x => ?_)
      refine Quotient.ind' (fun y hxy => ?_)
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      have hrel : QuotientGroup.leftRel J (f x) (f y) :=
        Quotient.eq''.mp hxy
      have hmap : f (x⁻¹ * y) ∈ J := by
        rw [f.map_mul, f.map_inv]
        exact QuotientGroup.leftRel_apply.mp hrel
      have hmem : x⁻¹ * y ∈ J.comap f := hmap
      rwa [hcomap] at hmem
    · refine Quotient.ind' (fun q => ?_)
      obtain ⟨x, hx⟩ := hquot q
      exact ⟨QuotientGroup.mk x, hx⟩
  let e : P ⧸ H ≃ Q ⧸ J := Equiv.ofBijective qf hqf
  have he (x : P) : e (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl
  have hsmul (x : P) (q : P ⧸ H) : e (x • q) = f x • e q := by
    refine Quotient.inductionOn' q ?_
    intro y
    simp only [MulAction.Quotient.smul_mk, he, smul_eq_mul, map_mul]
  let T : H.LeftTransversal := default
  let ρ : Q ⧸ J → Q := fun q =>
    f (T.property.leftQuotientEquiv (e.symm q) : P)
  have hρ (q : Q ⧸ J) : (ρ q : Q ⧸ J) = q := by
    change e (QuotientGroup.mk (T.property.leftQuotientEquiv (e.symm q) : P)) = q
    exact (congrArg e (T.property.leftQuotientEquiv.symm_apply_apply (e.symm q))).trans
      (e.apply_symm_apply q)
  let T' : J.LeftTransversal :=
    ⟨Set.range ρ, Subgroup.isComplement_range_left hρ⟩
  have hrep (q : P ⧸ H) :
      (T'.property.leftQuotientEquiv (e q) : Q) =
        f (T.property.leftQuotientEquiv q : P) := by
    change ((Subgroup.isComplement_range_left hρ).leftQuotientEquiv (e q) : Q) = _
    rw [Subgroup.IsComplement.leftQuotientEquiv_apply hρ (e q)]
    change f (T.property.leftQuotientEquiv (e.symm (e q)) : P) = _
    rw [e.symm_apply_apply]
  let : Fintype (P ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let : Fintype (Q ⧸ J) := J.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def _ T p, MonoidHom.transfer_def χ T' (f p)]
  simp only [Subgroup.leftTransversals.diff]
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro q _
  apply congrArg χ
  apply Subtype.ext
  change f ((T.property.leftQuotientEquiv q : P)⁻¹ *
      ((p • T).property.leftQuotientEquiv q : P)) =
    (T'.property.leftQuotientEquiv (e q) : Q)⁻¹ *
      ((f p • T').property.leftQuotientEquiv (e q) : Q)
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  rw [← f.map_inv p, ← hsmul (p⁻¹) q, hrep q, hrep (p⁻¹ • q)]
  simp only [map_mul, map_inv]

/-- Character-valued transfer commutes with an actual surjective quotient
whose kernel is contained in the finite-index subgroup. -/
theorem transfer_character_natural_of_surjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) [H.FiniteIndex]
    (χ : H.map f →* A) (p : P) :
    let _ : (H.map f).FiniteIndex :=
      Subgroup.FiniteIndex.map_of_surjective (H := H) (f := f) hf
    MonoidHom.transfer (χ.comp (f.subgroupMap H)) p =
      MonoidHom.transfer χ (f p) := by
  intro hindex
  have hcomap := Subgroup.comap_map_eq_self hker
  have hquot (q : Q) : ∃ x : P, (f x : Q ⧸ H.map f) = (q : Q ⧸ H.map f) := by
    obtain ⟨x, rfl⟩ := hf q
    exact ⟨x, rfl⟩
  have hmap : (f.comp H.subtype).codRestrict (H.map f)
      (fun x => show (x : P) ∈ (H.map f).comap f from hcomap.symm ▸ x.property) =
        f.subgroupMap H := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  have h := transfer_character_natural_of_coset_surjective f H (H.map f) hcomap hquot χ p
  rwa [hmap] at h

end ClassFormation

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

variable {G Q A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    [TopologicalSpace A] [CommGroup A] [T1Space A]

/-- The actual character obtained by restricting a continuous quotient map
to the open subgroup and then applying a character of its image. -/
def quotientSubgroupCharacter
    (N : OpenNormalSubgroup G) (f : G →ₜ* Q)
    (χ : (N : Subgroup G).map f.toMonoidHom →* A) :
    (N : Subgroup G) →ₜ* A where
  toMonoidHom := χ.comp (f.toMonoidHom.subgroupMap (N : Subgroup G))
  continuous_toFun := (continuous_of_discreteTopology : Continuous χ).comp
    (Continuous.subtype_mk (f.continuous_toFun.comp continuous_subtype_val)
      (fun n => ⟨n.val, n.property, rfl⟩))

/-- Every finite/discrete quotient computes the original topological
transfer by the original ordinary transfer of its subgroup image. -/
theorem lift_openNormalTransfer_discreteQuotient
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hker : f.toMonoidHom.ker ≤ (N : Subgroup G))
    (χ : (N : Subgroup G).map f.toMonoidHom →* A) :
    let _ : (N : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    let _ : ((N : Subgroup G).map f.toMonoidHom).FiniteIndex :=
      Subgroup.FiniteIndex.map_of_surjective (H := (N : Subgroup G))
        (f := f.toMonoidHom) hf
    (TopologicalAbelianization.lift (quotientSubgroupCharacter N f χ)).comp
        (openNormalTransferTopologicalAbelianization N) =
      TopologicalAbelianization.lift
        { toMonoidHom := (MonoidHom.transfer χ).comp f.toMonoidHom
          continuous_toFun := (continuous_of_discreteTopology :
            Continuous (MonoidHom.transfer χ)).comp f.continuous_toFun } := by
  intro hindex himage
  apply TopologicalAbelianization.hom_ext
  intro g
  change TopologicalAbelianization.lift (quotientSubgroupCharacter N f χ)
    (openNormalTransferTopologicalAbelianization N (TopologicalAbelianization.mk G g)) =
    MonoidHom.transfer χ (f g)
  rw [lift_openNormalTransfer_apply_mk]
  exact ClassFormation.transfer_character_natural_of_surjective f.toMonoidHom hf
    (N : Subgroup G) hker χ g

end ProCGroups.FiniteStepSolvableQuotients
