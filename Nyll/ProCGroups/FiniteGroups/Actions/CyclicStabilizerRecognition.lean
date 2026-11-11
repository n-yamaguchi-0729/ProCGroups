/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Recognition of finite actions with cyclic stabilizers

Burnside's formula on cyclic subgroups recovers their fixed-point counts from
the orbit counts on all subgroups. If point stabilizers are cyclic, a noncyclic
subgroup fixes no points. Thus these orbit counts recover all subgroup marks.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MulAction

private theorem equal_values_of_equal_sums {ι : Type*} [Fintype ι]
    (f g : ι → ℕ) (a b : ℕ) (hsum : ∑ i, f i = ∑ i, g i)
    (hvalues : ∀ i, f i = g i ∨ (f i = a ∧ g i = b))
    (i : ι) (hi : f i = a) (hi' : g i = b) : a = b := by
  classical
  rcases le_total a b with hab | hba
  · have hle : ∀ j ∈ Finset.univ, f j ≤ g j := by
      intro j _
      rcases hvalues j with h | ⟨hf, hg⟩
      · exact h.le
      · rw [hf, hg]
        exact hab
    exact hi.symm.trans
      (((Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)).trans hi')
  · have hle : ∀ j ∈ Finset.univ, g j ≤ f j := by
      intro j _
      rcases hvalues j with h | ⟨hf, hg⟩
      · exact h.ge
      · rw [hf, hg]
        exact hba
    exact (hi'.symm.trans
      (((Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm i (Finset.mem_univ i)).trans hi)).symm

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

private theorem card_fixedBy_subgroup (H : Subgroup G) (h : H) :
    Nat.card (fixedBy X h) = Nat.card (fixedBy X (h : G)) := by
  apply Nat.card_congr
  exact Set.equivOfEq (show fixedBy X h = fixedBy X (h : G) from rfl)

/-- Fixing a generator is equivalent to fixing its whole cyclic subgroup. -/
theorem fixedPoints_zpowers_eq_fixedBy (g : G) :
    fixedPoints (Subgroup.zpowers g) X = fixedBy X g := by
  ext x
  constructor
  · intro hx
    exact hx ⟨g, Subgroup.mem_zpowers g⟩
  · intro hx h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.property
    change (h : G) • x = x
    rw [← hn]
    exact mem_fixedBy_zpow hx n

/-- All subgroup orbit counts determine the marks at cyclic subgroups.
No restriction on the point stabilizers is needed for this step. -/
theorem card_fixedPoints_eq_of_card_orbits_eq_of_isCyclic
    [Finite G] [Finite X] [Finite Y]
    (horbits : ∀ H : Subgroup G,
      Nat.card (orbitRel.Quotient H X) = Nat.card (orbitRel.Quotient H Y))
    (H : Subgroup G) (hH : IsCyclic H) :
    Nat.card (fixedPoints H X) = Nat.card (fixedPoints H Y) := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let _ : Fintype Y := Fintype.ofFinite Y
  have aux : ∀ n (K : Subgroup G), Nat.card K = n → IsCyclic K →
      Nat.card (fixedPoints K X) = Nat.card (fixedPoints K Y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hcard hK
      let _ : Fintype K := Fintype.ofFinite K
      obtain ⟨g, hg⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp hK
      have hgm : g ∈ K := hg ▸ Subgroup.mem_zpowers g
      have hsum : (∑ h : K, Nat.card (fixedBy X (h : G))) =
          ∑ h : K, Nat.card (fixedBy Y (h : G)) := by
        have hburnX : (∑ h : K, Nat.card (fixedBy X h)) =
            Nat.card (orbitRel.Quotient K X) * Nat.card K := by
          simpa only [Nat.card_eq_fintype_card] using
            sum_card_fixedBy_eq_card_orbits_mul_card_group K X
        have hburnY : (∑ h : K, Nat.card (fixedBy Y h)) =
            Nat.card (orbitRel.Quotient K Y) * Nat.card K := by
          simpa only [Nat.card_eq_fintype_card] using
            sum_card_fixedBy_eq_card_orbits_mul_card_group K Y
        calc
          _ = ∑ h : K, Nat.card (fixedBy X h) := by
            apply Finset.sum_congr rfl
            intro h _
            exact (card_fixedBy_subgroup (X := X) K h).symm
          _ = Nat.card (orbitRel.Quotient K X) * Nat.card K := hburnX
          _ = Nat.card (orbitRel.Quotient K Y) * Nat.card K := by rw [horbits K]
          _ = ∑ h : K, Nat.card (fixedBy Y h) := hburnY.symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro h _
            exact card_fixedBy_subgroup (X := Y) K h
      have hvalues : ∀ h : K,
          Nat.card (fixedBy X (h : G)) = Nat.card (fixedBy Y (h : G)) ∨
          (Nat.card (fixedBy X (h : G)) = Nat.card (fixedPoints K X) ∧
            Nat.card (fixedBy Y (h : G)) = Nat.card (fixedPoints K Y)) := by
        intro h
        by_cases hh : Subgroup.zpowers (h : G) = K
        · right
          constructor
          · rw [← fixedPoints_zpowers_eq_fixedBy (X := X) (h : G), hh]
          · rw [← fixedPoints_zpowers_eq_fixedBy (X := Y) (h : G), hh]
        · left
          have hle : Subgroup.zpowers (h : G) ≤ K :=
            Subgroup.zpowers_le.mpr h.property
          have hlt : Subgroup.zpowers (h : G) < K :=
            lt_iff_le_not_ge.mpr ⟨hle, fun hge => hh (le_antisymm hle hge)⟩
          have hn : Nat.card (Subgroup.zpowers (h : G)) < n := by
            rw [← hcard]
            exact Subgroup.card_lt_of_lt hlt
          have heq := ih (Nat.card (Subgroup.zpowers (h : G))) hn
            (Subgroup.zpowers (h : G)) rfl inferInstance
          simpa only [fixedPoints_zpowers_eq_fixedBy] using heq
      apply equal_values_of_equal_sums
        (fun h : K => Nat.card (fixedBy X (h : G)))
        (fun h : K => Nat.card (fixedBy Y (h : G)))
        (Nat.card (fixedPoints K X)) (Nat.card (fixedPoints K Y))
        hsum hvalues ⟨g, hgm⟩
      · rw [← fixedPoints_zpowers_eq_fixedBy (X := X) g, hg]
      · rw [← fixedPoints_zpowers_eq_fixedBy (X := Y) g, hg]
  exact aux (Nat.card H) H rfl hH

/-- Cyclic point stabilizers exclude fixed points of noncyclic subgroups. -/
theorem isEmpty_fixedPoints_of_not_isCyclic
    (hstab : ∀ x : X, IsCyclic (stabilizer G x))
    (H : Subgroup G) (hH : ¬IsCyclic H) : IsEmpty (fixedPoints H X) := by
  refine ⟨fun x => hH ?_⟩
  have : IsCyclic (stabilizer G x.val) := hstab x.val
  apply Subgroup.isCyclic_of_le (H' := stabilizer G x.val)
  intro g hg
  exact x.property ⟨g, hg⟩

/-- For finite actions with cyclic point stabilizers, equality of all subgroup
orbit counts implies equality of every subgroup fixed-point count. -/
theorem card_fixedPoints_eq_of_card_orbits_eq_of_cyclic_stabilizers
    [Finite G] [Finite X] [Finite Y]
    (hX : ∀ x : X, IsCyclic (stabilizer G x))
    (hY : ∀ y : Y, IsCyclic (stabilizer G y))
    (horbits : ∀ H : Subgroup G,
      Nat.card (orbitRel.Quotient H X) = Nat.card (orbitRel.Quotient H Y))
    (H : Subgroup G) :
    Nat.card (fixedPoints H X) = Nat.card (fixedPoints H Y) := by
  classical
  by_cases hH : IsCyclic H
  · exact card_fixedPoints_eq_of_card_orbits_eq_of_isCyclic horbits H hH
  · have hXzero : Nat.card (fixedPoints H X) = 0 :=
      Finite.card_eq_zero_iff.mpr (isEmpty_fixedPoints_of_not_isCyclic hX H hH)
    have hYzero : Nat.card (fixedPoints H Y) = 0 :=
      Finite.card_eq_zero_iff.mpr (isEmpty_fixedPoints_of_not_isCyclic hY H hH)
    exact hXzero.trans hYzero.symm

end MulAction
