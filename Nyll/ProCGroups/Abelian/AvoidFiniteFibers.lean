/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.GroupTheory.Index

/-! # Simultaneous avoidance in a finite group -/

@[expose] public section

open scoped BigOperators

namespace ProCGroups.Abelian

private theorem card_filter_eq_le_card_ker {A B : Type*} [Group A] [Fintype A] [Group B]
    (f : A →* B) (b : B) [DecidablePred (fun a => f a = b)] :
    (Finset.univ.filter (fun a => f a = b)).card ≤ Nat.card f.ker := by
  classical
  let s := Finset.univ.filter (fun a => f a = b)
  change s.card ≤ Nat.card f.ker
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hx' : f x = b := (Finset.mem_filter.mp hx).2
    let e : {a // a ∈ s} → f.ker := fun a => ⟨a.1 / x, by
      have ha : f a.1 = b := (Finset.mem_filter.mp a.2).2
      rw [MonoidHom.mem_ker, map_div, ha, hx', div_self']⟩
    have he : Function.Injective e := by
      intro a c h
      apply Subtype.ext
      exact div_left_injective (congrArg Subtype.val h)
    rw [← Fintype.card_coe s, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective e he
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    exact Nat.zero_le _

/-- If each homomorphism has more values than the number of conditions, one group
element avoids all the prescribed values. The prescribed values need not be identities. -/
theorem exists_forall_apply_ne_of_card_lt_card_range
    {ι A B : Type*} [Fintype ι] [Group A] [Finite A] [Group B]
    (f : ι → A →* B) (b : ι → B)
    (h : ∀ i, Fintype.card ι < Nat.card (f i).range) :
    ∃ a, ∀ i, f i a ≠ b i := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let s : ι → Finset A := fun i => Finset.univ.filter (fun a => f i a = b i)
  by_contra! hcover
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨i, _⟩ := hcover 1
    exact ⟨i, Finset.mem_univ _⟩
  have hsubset : (Finset.univ : Finset A) ⊆ Finset.univ.biUnion s := by
    intro a _
    obtain ⟨i, hi⟩ := hcover a
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hle : Fintype.card A ≤ ∑ i, (s i).card := by
    rw [← Finset.card_univ]
    exact (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hlt (i : ι) : (s i).card * Fintype.card ι < Fintype.card A := by
    calc
      (s i).card * Fintype.card ι ≤ Nat.card (f i).ker * Fintype.card ι :=
        Nat.mul_le_mul_right _ (card_filter_eq_le_card_ker (f i) (b i))
      _ < Nat.card (f i).ker * Nat.card (f i).range :=
        Nat.mul_lt_mul_of_pos_left (h i) Nat.card_pos
      _ = Fintype.card A := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsum := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlt i)
  rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  change (∑ i, (s i).card) * Fintype.card ι < Fintype.card ι * Fintype.card A at hsum
  rw [Nat.mul_comm (Fintype.card ι) (Fintype.card A)] at hsum
  exact (not_lt_of_ge (Nat.mul_le_mul_right (Fintype.card ι) hle)) hsum

end ProCGroups.Abelian
