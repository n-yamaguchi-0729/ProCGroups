/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalTransferComparison

/-!
# Continuous transfer for open subgroups of finite index

Mathlib's transfer is continuous for the quotient topology on the
abelianization. The proof uses the discrete left coset space.
-/

@[expose] public section

open scoped Pointwise

namespace ProCGroups.Abelian

open ProCGroups.ProC

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : OpenSubgroup G) [Finite (G ⧸ (H : Subgroup G))]

local instance (U : OpenSubgroup G) : IsTopologicalGroup U :=
  inferInstanceAs (IsTopologicalGroup U.toSubgroup)

/-- The contribution of a single left coset to the ordinary transfer. -/
def openSubgroupTransferTerm (q : G ⧸ (H : Subgroup G)) (g : G) : H :=
  let rho := quotientOpenSubgroupSection (H : Subgroup G)
  ⟨(rho (g • q))⁻¹ * g * rho q, by
    have hrho := quotientOpenSubgroupSection_rightInverse (H : Subgroup G)
    have h :
        (QuotientGroup.mk (rho (g • q)) : G ⧸ (H : Subgroup G)) =
          QuotientGroup.mk (g * rho q) := by
      calc
        QuotientGroup.mk (rho (g • q)) = g • q := hrho (g • q)
        _ = g • (QuotientGroup.mk (rho q) : G ⧸ (H : Subgroup G)) :=
          congrArg (fun y : G ⧸ (H : Subgroup G) => g • y) (hrho q).symm
        _ = QuotientGroup.mk (g * rho q) :=
          MulAction.Quotient.smul_mk H.toSubgroup g (rho q)
    change (rho (g • q))⁻¹ * g * rho q ∈ (H : Subgroup G)
    simpa only [mul_assoc] using (QuotientGroup.leftRel_apply.mp (Quotient.exact' h))⟩

omit [Finite (G ⧸ (H : Subgroup G))] in
theorem openSubgroupTransferTerm_continuous (q : G ⧸ (H : Subgroup G)) :
    Continuous (openSubgroupTransferTerm H q) := by
  let rho := quotientOpenSubgroupSection (H : Subgroup G)
  let : DiscreteTopology (G ⧸ (H : Subgroup G)) := QuotientGroup.discreteTopology H.isOpen'
  have hrho : Continuous rho := continuous_of_discreteTopology
  have hq : Continuous (fun g : G => g • q) := by
    have h :
        (fun g : G => g • q) =
          fun g : G => (QuotientGroup.mk (g * rho q) : G ⧸ (H : Subgroup G)) := by
      funext g
      have hq' : (QuotientGroup.mk (rho q) : G ⧸ (H : Subgroup G)) = q :=
        quotientOpenSubgroupSection_rightInverse (H : Subgroup G) q
      exact (congrArg (fun y : G ⧸ (H : Subgroup G) => g • y) hq').symm.trans
        (MulAction.Quotient.smul_mk H.toSubgroup g (rho q))
    rw [h]
    exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  exact (((hrho.comp hq).inv.mul continuous_id).mul continuous_const).subtype_mk _

omit [Finite (G ⧸ (H : Subgroup G))] in
theorem openSubgroupTransfer_mk_eq_prod
    [(H : Subgroup G).FiniteIndex] (g : G) :
    let : Fintype (G ⧸ (H : Subgroup G)) := (H : Subgroup G).fintypeQuotientOfFiniteIndex
    MonoidHom.transfer (TopologicalAbelianization.mk H) g =
      ∏ q : G ⧸ (H : Subgroup G),
        TopologicalAbelianization.mk H (openSubgroupTransferTerm H q g) := by
  classical
  let : Fintype (G ⧸ (H : Subgroup G)) := (H : Subgroup G).fintypeQuotientOfFiniteIndex
  let m := TopologicalAbelianization.mk H
  let rho : G ⧸ (H : Subgroup G) → G := quotientOpenSubgroupSection (H : Subgroup G)
  have hrho : ∀ q : G ⧸ (H : Subgroup G), (rho q : G ⧸ (H : Subgroup G)) = q :=
    quotientOpenSubgroupSection_rightInverse (H : Subgroup G)
  let T : (H : Subgroup G).LeftTransversal :=
    ⟨Set.range rho, Subgroup.isComplement_range_left hrho⟩
  have hT (q : G ⧸ (H : Subgroup G)) :
      (T.property.leftQuotientEquiv q : G) = rho q :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hrho q
  let eta (q : G ⧸ (H : Subgroup G)) : H :=
    ⟨(T.property.leftQuotientEquiv q : G)⁻¹ *
        ((g • T).property.leftQuotientEquiv q : G),
      QuotientGroup.leftRel_apply.mp (Quotient.exact'
        ((T.property.leftQuotientEquiv.symm_apply_apply q).trans
          ((g • T).property.leftQuotientEquiv.symm_apply_apply q).symm))⟩
  have hterm (q : G ⧸ (H : Subgroup G)) :
      openSubgroupTransferTerm H q g = eta (g • q) := by
    apply Subtype.ext
    change (rho (g • q))⁻¹ * g * rho q =
      (T.property.leftQuotientEquiv (g • q) : G)⁻¹ *
        ((g • T).property.leftQuotientEquiv (g • q) : G)
    simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, inv_smul_smul, hT, smul_eq_mul]
    exact mul_assoc _ _ _
  change MonoidHom.transfer m g =
    ∏ q : G ⧸ (H : Subgroup G), m (openSubgroupTransferTerm H q g)
  symm
  rw [MonoidHom.transfer_def _ T g]
  change (∏ q : G ⧸ (H : Subgroup G), m (openSubgroupTransferTerm H q g)) =
    ∏ q : G ⧸ (H : Subgroup G), m (eta q)
  calc
    (∏ q : G ⧸ (H : Subgroup G), m (openSubgroupTransferTerm H q g)) =
        ∏ q : G ⧸ (H : Subgroup G), m (eta (g • q)) :=
      Finset.prod_congr rfl fun q _ => congrArg m (hterm q)
    _ = ∏ q : G ⧸ (H : Subgroup G), m (eta q) :=
      Equiv.prod_comp (MulAction.toPerm g) (fun q => m (eta q))

/-- The algebraic transfer to the topological abelianization is continuous. -/
noncomputable def openSubgroupTransferPre : G →ₜ* TopologicalAbelianization H := by
  classical
  let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : Fintype (G ⧸ (H : Subgroup G)) := (H : Subgroup G).fintypeQuotientOfFiniteIndex
  let m := TopologicalAbelianization.mk H
  refine ⟨MonoidHom.transfer m, ?_⟩
  have hc : Continuous (fun g : G => ∏ q : G ⧸ (H : Subgroup G),
      m (openSubgroupTransferTerm H q g)) :=
    continuous_finsetProd Finset.univ fun q _ =>
      (TopologicalAbelianization.mkₜ H).continuous.comp (openSubgroupTransferTerm_continuous H q)
  exact hc.congr fun g => (openSubgroupTransfer_mk_eq_prod H g).symm

/-- The same group-theoretic transfer factors through the closed commutator. -/
noncomputable def openSubgroupTransfer :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization H :=
  TopologicalAbelianization.lift (openSubgroupTransferPre H)

theorem openSubgroupTransfer_apply_mk (g : G) :
    let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    openSubgroupTransfer H (TopologicalAbelianization.mk G g) =
      MonoidHom.transfer (TopologicalAbelianization.mk H) g :=
  rfl

/-- Applying a continuous character to transfer is the algebraic transfer of
the same character on the open subgroup. -/
theorem lift_openSubgroupTransfer_apply_mk
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (chi : H →ₜ* A) (g : G) :
    let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    TopologicalAbelianization.lift chi (openSubgroupTransfer H (TopologicalAbelianization.mk G g)) =
      MonoidHom.transfer chi.toMonoidHom g := by
  intro hindex
  rw [openSubgroupTransfer_apply_mk]
  change (TopologicalAbelianization.lift chi).toMonoidHom
      (MonoidHom.transfer (TopologicalAbelianization.mk H) g) = _
  rw [MonoidHom.map_transfer_eq_transfer_comp]
  rfl

/-- Transfer commutes with a continuous map inducing the same finite coset
space, including a dense map and the pullback of an open subgroup. -/
theorem openSubgroupTransfer_natural_of_coset_surjective
    {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (J : OpenSubgroup Q) [Finite (Q ⧸ (J : Subgroup Q))]
    (f : G →ₜ* Q) (hcomap : (J : Subgroup Q).comap f.toMonoidHom = (H : Subgroup G))
    (hquot : ∀ q : Q, ∃ p : G,
      (QuotientGroup.mk (f p) : Q ⧸ (J : Subgroup Q)) = QuotientGroup.mk q)
    (fH : H →ₜ* J) (hfH : ∀ x : H, (fH x : Q) = f x)
    (z : TopologicalAbelianization G) :
    TopologicalAbelianization.map fH (openSubgroupTransfer H z) =
      openSubgroupTransfer J (TopologicalAbelianization.map f z) := by
  let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : (J : Subgroup Q).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let r : H →* J := (f.toMonoidHom.comp (H : Subgroup G).subtype).codRestrict
    (J : Subgroup Q) (fun x => show (x : G) ∈ (J : Subgroup Q).comap f.toMonoidHom from
      hcomap.symm ▸ x.property)
  have hr : fH.toMonoidHom = r := by
    exact MonoidHom.ext fun x => Subtype.ext (hfH x)
  obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk G z
  change TopologicalAbelianization.lift ((TopologicalAbelianization.mkₜ J).comp fH)
      (openSubgroupTransfer H (TopologicalAbelianization.mk G g)) =
    openSubgroupTransfer J (TopologicalAbelianization.mk Q (f g))
  rw [lift_openSubgroupTransfer_apply_mk, openSubgroupTransfer_apply_mk]
  change MonoidHom.transfer ((TopologicalAbelianization.mk J).comp fH.toMonoidHom) g = _
  rw [hr]
  exact ClassFormation.transfer_character_natural_of_coset_surjective f.toMonoidHom
    (H : Subgroup G) (J : Subgroup Q) hcomap hquot (TopologicalAbelianization.mk J) g

/-- Compute the character of transfer after identifying the open subgroup with
another topological group. -/
theorem lift_openSubgroupTransfer_congr_apply_mk
    {X A : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CommGroup A] [TopologicalSpace A] [T1Space A]
    (k : H ≃ₜ* X) (χ : X →ₜ* A) (g : G) :
    let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    TopologicalAbelianization.lift χ
        (TopologicalAbelianization.congr k (openSubgroupTransfer H
          (TopologicalAbelianization.mk G g))) =
      MonoidHom.transfer (χ.toMonoidHom.comp k.toMulEquiv.toMonoidHom) g := by
  intro hindex
  let χH := χ.comp (ContinuousMonoidHom.toContinuousMonoidHom k)
  have hLift (x : TopologicalAbelianization H) :
      TopologicalAbelianization.lift χ (TopologicalAbelianization.congr k x) =
        TopologicalAbelianization.lift χH x := by
    obtain ⟨t, rfl⟩ := TopologicalAbelianization.surjective_mk H x
    rfl
  exact (hLift (openSubgroupTransfer H (TopologicalAbelianization.mk G g))).trans
    (lift_openSubgroupTransfer_apply_mk H χH g)

/-- Natural transfer when the ambient and upper groups are identified by
compatible topological isomorphisms. -/
theorem openSubgroupTransfer_congr_of_inclusion
    {Q X Y : Type*} [Group Q] [Group X] [Group Y]
    [TopologicalSpace Q] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup Q] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    (J : OpenSubgroup Q) [Finite (Q ⧸ (J : Subgroup Q))]
    (k : H ≃ₜ* X) (l : J ≃ₜ* Y)
    (f : G ≃ₜ* Q) (g : X ≃ₜ* Y) (h : ∀ a : H, ((l.symm (g (k a)) : J) : Q) = f a)
    (z : TopologicalAbelianization G) :
    TopologicalAbelianization.congr g
        (TopologicalAbelianization.congr k (openSubgroupTransfer H z)) =
      TopologicalAbelianization.congr l
        (openSubgroupTransfer J (TopologicalAbelianization.congr f z)) := by
  let e : H ≃ₜ* J := (k.trans g).trans l.symm
  let e₀ := ContinuousMonoidHom.toContinuousMonoidHom e
  let f₀ := ContinuousMonoidHom.toContinuousMonoidHom f
  have hcomap : (J : Subgroup Q).comap f₀.toMonoidHom = (H : Subgroup G) := by
    ext a
    change f a ∈ J ↔ a ∈ H
    constructor
    · intro ha
      let b := e.symm ⟨f a, ha⟩
      have hb : f (b : G) = f a :=
        (h b).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨f a, ha⟩))
      exact f.injective hb ▸ b.property
    · intro ha
      exact h ⟨a, ha⟩ ▸ (e ⟨a, ha⟩).property
  have hquot (q : Q) : ∃ a : G,
      (QuotientGroup.mk (f₀ a) : Q ⧸ (J : Subgroup Q)) = QuotientGroup.mk q := by
    obtain ⟨a, rfl⟩ := f.surjective q
    exact ⟨a, rfl⟩
  have hmap (x : TopologicalAbelianization H) :
      TopologicalAbelianization.congr g (TopologicalAbelianization.congr k x) =
        TopologicalAbelianization.congr l (TopologicalAbelianization.map e₀ x) := by
    obtain ⟨a, rfl⟩ := TopologicalAbelianization.surjective_mk H x
    rw [TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.congr_apply_mk,
      TopologicalAbelianization.map_apply_mk, TopologicalAbelianization.congr_apply_mk]
    exact congrArg (TopologicalAbelianization.mk Y) (l.apply_symm_apply (g (k a))).symm
  exact (hmap (openSubgroupTransfer H z)).trans
    (congrArg (TopologicalAbelianization.congr l)
      (openSubgroupTransfer_natural_of_coset_surjective H J f₀ hcomap hquot e₀ h z))

/-- Evaluating transfer by a character that extends to the ambient group
raises its original value to the index of the subgroup. -/
theorem openSubgroupTransfer_character (A : Type*) [CommGroup A] [TopologicalSpace A] [T1Space A]
    (chi : G →ₜ* A) (g : G) :
    TopologicalAbelianization.lift
      (chi.comp (⟨(H : Subgroup G).subtype, continuous_subtype_val⟩ : H →ₜ* G))
      (openSubgroupTransfer H (TopologicalAbelianization.mk G g)) =
      chi g ^ (H : Subgroup G).index := by
  classical
  let : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : Fintype (G ⧸ (H : Subgroup G)) := (H : Subgroup G).fintypeQuotientOfFiniteIndex
  let rho := quotientOpenSubgroupSection (H : Subgroup G)
  let chiH := chi.comp (⟨(H : Subgroup G).subtype, continuous_subtype_val⟩ : H →ₜ* G)
  change TopologicalAbelianization.lift chiH
    (openSubgroupTransfer H (TopologicalAbelianization.mk G g)) = _
  rw [openSubgroupTransfer_apply_mk, openSubgroupTransfer_mk_eq_prod, map_prod]
  simp only [TopologicalAbelianization.lift_apply_mk]
  change (∏ q : G ⧸ (H : Subgroup G), chi ((rho (g • q))⁻¹ * g * rho q)) = _
  simp only [map_mul, map_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_const, Finset.card_univ]
  rw [show (∏ q : G ⧸ (H : Subgroup G), chi (rho (g • q))) =
      ∏ q : G ⧸ (H : Subgroup G), chi (rho q) from
    Equiv.prod_comp (MulAction.toPerm g) (fun q => chi (rho q)), ← Nat.card_eq_fintype_card]
  let r := ∏ q : G ⧸ (H : Subgroup G), chi (rho q)
  change r⁻¹ * chi g ^ (H : Subgroup G).index * r = _
  rw [mul_assoc, mul_comm (chi g ^ (H : Subgroup G).index), inv_mul_cancel_left]

end
end ProCGroups.Abelian
