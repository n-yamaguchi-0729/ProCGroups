/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Equiv.Set
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite actions are determined by their subgroup fixed-point counts

The proof matches an orbit whose stabilizer has maximal order, cancels that
orbit from the fixed-point counts, and proceeds on the invariant complements.
The bijection is constructed on the original actions.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MulAction

variable {G : Type u} [Group G]
variable {X : Type v} {Y : Type w} [MulAction G X] [MulAction G Y]

private def fixedPointsBotEquiv (X : Type v) [MulAction G X] :
    fixedPoints (⊥ : Subgroup G) X ≃ X where
  toFun := Subtype.val
  invFun x := ⟨x, fun g => by
    change (g : G) • x = x
    rw [Subgroup.mem_bot.mp g.property, one_smul]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- An actual equivariant bijection preserves every subgroup mark. -/
theorem card_fixedPoints_eq_of_equivariant_equiv (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (H : Subgroup G) :
    Nat.card (fixedPoints H X) = Nat.card (fixedPoints H Y) := by
  apply Nat.card_congr
  refine e.subtypeEquiv fun x => ?_
  constructor
  · intro hx h
    change (h : G) • e x = e x
    rw [← he (h : G) x]
    exact congrArg e (hx h)
  · intro hy h
    change (h : G) • x = x
    apply e.injective
    exact (he (h : G) x).trans (hy h)

private theorem smul_eq_of_stabilizer_le {x : X} {y : Y}
    (h : stabilizer G x ≤ stabilizer G y) {a b : G}
    (hab : a • x = b • x) : a • y = b • y := by
  have hx : b⁻¹ * a ∈ stabilizer G x := by
    change (b⁻¹ * a) • x = x
    rw [mul_smul, hab, inv_smul_smul]
  have hy : (b⁻¹ * a) • y = y := h hx
  calc
    a • y = b • ((b⁻¹ * a) • y) := by rw [smul_smul, mul_inv_cancel_left]
    _ = b • y := congrArg (b • ·) hy

private theorem exists_orbit_equiv_of_stabilizer_eq (x : X) (y : Y)
    (h : stabilizer G x = stabilizer G y) :
    ∃ e : orbit G x ≃ orbit G y, ∀ (g : G) (a : orbit G x), e (g • a) = g • e a := by
  let f : orbit G x → orbit G y := fun a =>
    ⟨a.property.choose • y, mem_orbit y a.property.choose⟩
  have hf (a : orbit G x) (g : G) (hg : g • x = a.val) : (f a : Y) = g • y :=
    smul_eq_of_stabilizer_le h.le (a.property.choose_spec.trans hg.symm)
  have hinj : Function.Injective f := by
    intro a b hab
    have hsmul : a.property.choose • y = b.property.choose • y :=
      congrArg Subtype.val hab
    apply Subtype.ext
    exact a.property.choose_spec.symm.trans
      ((smul_eq_of_stabilizer_le h.ge hsmul).trans b.property.choose_spec)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := b.property
    refine ⟨⟨g • x, mem_orbit x g⟩, ?_⟩
    exact Subtype.ext ((hf _ g rfl).trans hg)
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro g a
  have ha : a.property.choose • x = (a : X) := a.property.choose_spec
  apply Subtype.ext
  change (f (g • a) : Y) = g • (f a : Y)
  calc
    _ = (g * a.property.choose) • y := hf (g • a) (g * a.property.choose)
      ((mul_smul g a.property.choose x).trans (congrArg (g • ·) ha))
    _ = _ := mul_smul g a.property.choose y

private def orbitSubMulAction (x : X) : SubMulAction G X where
  carrier := orbit G x
  smul_mem' := fun g _ hx => mem_orbit_of_mem_orbit g hx

private theorem card_fixedPoints_add_compl [Finite X]
    (s : SubMulAction G X) (H : Subgroup G) :
    Nat.card (fixedPoints H X) =
      Nat.card (fixedPoints H s) +
        Nat.card (fixedPoints H (sᶜ : SubMulAction G X)) := by
  classical
  let f : fixedPoints H s ⊕ fixedPoints H (sᶜ : SubMulAction G X) → fixedPoints H X :=
    Sum.elim
      (fun a => ⟨a.val.val, fun h => congrArg Subtype.val (a.property h)⟩)
      (fun a => ⟨a.val.val, fun h => congrArg Subtype.val (a.property h)⟩)
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hval : a.val.val = b.val.val :=
          congrArg (fun z : fixedPoints H X => z.val) hab
        apply congrArg Sum.inl
        apply Subtype.ext
        apply Subtype.ext
        exact hval
      | inr b =>
        exact False.elim (b.val.property ((congrArg Subtype.val hab) ▸ a.val.property))
    | inr a =>
      cases b with
      | inl b =>
        exact False.elim (a.val.property ((congrArg Subtype.val hab).symm ▸ b.val.property))
      | inr b =>
        have hval : a.val.val = b.val.val :=
          congrArg (fun z : fixedPoints H X => z.val) hab
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        exact hval
  have hsurj : Function.Surjective f := by
    intro a
    by_cases ha : a.val ∈ s
    · refine ⟨Sum.inl ⟨⟨a.val, ha⟩, fun h => Subtype.ext (a.property h)⟩, ?_⟩
      exact Subtype.ext rfl
    · refine ⟨Sum.inr ⟨⟨a.val, ha⟩, fun h => Subtype.ext (a.property h)⟩, ?_⟩
      exact Subtype.ext rfl
  rw [← Nat.card_sum]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

private theorem exists_equiv_of_subaction_and_compl
    (s : SubMulAction G X) (t : SubMulAction G Y)
    (e : s ≃ t) (he : ∀ (g : G) (x : s), e (g • x) = g • e x)
    (ec : (sᶜ : SubMulAction G X) ≃ (tᶜ : SubMulAction G Y))
    (hec : ∀ (g : G) (x : (sᶜ : SubMulAction G X)), ec (g • x) = g • ec x) :
    ∃ e' : X ≃ Y, ∀ (g : G) (x : X), e' (g • x) = g • e' x := by
  classical
  let e' : X ≃ Y := ((Equiv.Set.sumCompl (s : Set X)).symm.trans
    (e.sumCongr ec)).trans (Equiv.Set.sumCompl (t : Set Y))
  refine ⟨e', ?_⟩
  intro g x
  by_cases hx : x ∈ s
  · have hg : g • x ∈ s := s.smul_mem g hx
    simp only [e', Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hx,
      Equiv.Set.sumCompl_symm_apply_of_mem hg, Equiv.sumCongr_apply, Sum.map_inl]
    exact congrArg Subtype.val (he g ⟨x, hx⟩)
  · have hg : g • x ∈ (sᶜ : SubMulAction G X) :=
      (sᶜ : SubMulAction G X).smul_mem g hx
    simp only [e', Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hx,
      Equiv.Set.sumCompl_symm_apply_of_notMem hg, Equiv.sumCongr_apply, Sum.map_inr]
    exact congrArg Subtype.val (hec g ⟨x, hx⟩)

private theorem exists_equal_stabilizers_of_marks [Finite G] [Finite X] [Finite Y]
    [Nonempty X]
    (hmarks : ∀ H : Subgroup G, Nat.card (fixedPoints H X) = Nat.card (fixedPoints H Y)) :
    ∃ (x : X) (y : Y), stabilizer G x = stabilizer G y := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ
    (fun a : X => Nat.card (stabilizer G a)) Finset.univ_nonempty
  have hX : Nonempty (fixedPoints (stabilizer G x) X) :=
    ⟨⟨x, fun g => g.property⟩⟩
  have hY : Nonempty (fixedPoints (stabilizer G x) Y) := by
    apply Finite.card_pos_iff.mp
    rw [← hmarks (stabilizer G x)]
    exact Finite.card_pos_iff.mpr hX
  obtain ⟨⟨y, hy⟩⟩ := hY
  have hxy : stabilizer G x ≤ stabilizer G y := fun g hg => hy ⟨g, hg⟩
  have hY' : Nonempty (fixedPoints (stabilizer G y) Y) :=
    ⟨⟨y, fun g => g.property⟩⟩
  have hX' : Nonempty (fixedPoints (stabilizer G y) X) := by
    apply Finite.card_pos_iff.mp
    rw [hmarks (stabilizer G y)]
    exact Finite.card_pos_iff.mpr hY'
  obtain ⟨⟨x', hx'⟩⟩ := hX'
  have hyx' : stabilizer G y ≤ stabilizer G x' := fun g hg => hx' ⟨g, hg⟩
  refine ⟨x, y, Subgroup.eq_of_le_of_card_ge hxy ?_⟩
  exact (Subgroup.card_le_of_le hyx').trans (hx x' (Finset.mem_univ x'))

/-- The fixed-point counts of all subgroups classify finite group actions.
The conclusion is a bijection of the original sets commuting with the original action. -/
theorem exists_equiv_of_card_fixedPoints_eq [Finite G] [Finite X] [Finite Y]
    (hmarks : ∀ H : Subgroup G, Nat.card (fixedPoints H X) = Nat.card (fixedPoints H Y)) :
    ∃ e : X ≃ Y, ∀ (g : G) (x : X), e (g • x) = g • e x := by
  classical
  suffices aux : ∀ n (A : Type v) (B : Type w) [MulAction G A] [MulAction G B]
      [Finite A] [Finite B], Nat.card A = n →
      (∀ H : Subgroup G, Nat.card (fixedPoints H A) = Nat.card (fixedPoints H B)) →
      ∃ e : A ≃ B, ∀ (g : G) (a : A), e (g • a) = g • e a from
    aux (Nat.card X) X Y rfl hmarks
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A B aA aB fA fB hcard hm
    rcases isEmpty_or_nonempty A with hA | hA
    · have hAB : Nat.card A = Nat.card B :=
        (Nat.card_congr (fixedPointsBotEquiv (G := G) A)).symm.trans
          ((hm ⊥).trans (Nat.card_congr (fixedPointsBotEquiv (G := G) B)))
      have : IsEmpty B := Finite.card_eq_zero_iff.mp
        (hAB.symm.trans (Finite.card_eq_zero_iff.mpr hA))
      exact ⟨Equiv.equivOfIsEmpty A B, fun _ a => isEmptyElim a⟩
    · obtain ⟨x, y, hxy⟩ := exists_equal_stabilizers_of_marks hm
      let s : SubMulAction G A := orbitSubMulAction x
      let t : SubMulAction G B := orbitSubMulAction y
      obtain ⟨e, he⟩ := exists_orbit_equiv_of_stabilizer_eq x y hxy
      have he' : ∀ (g : G) (a : s), e (g • a) = g • e a := he
      have hcmarks : ∀ H : Subgroup G,
          Nat.card (fixedPoints H (sᶜ : SubMulAction G A)) =
            Nat.card (fixedPoints H (tᶜ : SubMulAction G B)) := by
        intro H
        have htotal := hm H
        rw [card_fixedPoints_add_compl s H, card_fixedPoints_add_compl t H] at htotal
        have horbit := card_fixedPoints_eq_of_equivariant_equiv e he' H
        exact Nat.add_left_cancel (horbit ▸ htotal)
      have hlt : Nat.card (sᶜ : SubMulAction G A) < n := by
        rw [← hcard]
        apply Finite.card_subtype_lt (x := x)
        exact fun hx => hx (mem_orbit_self x)
      obtain ⟨ec, hec⟩ := ih (Nat.card (sᶜ : SubMulAction G A)) hlt
        (sᶜ : SubMulAction G A) (tᶜ : SubMulAction G B) rfl hcmarks
      exact exists_equiv_of_subaction_and_compl s t e he' ec hec

end MulAction
