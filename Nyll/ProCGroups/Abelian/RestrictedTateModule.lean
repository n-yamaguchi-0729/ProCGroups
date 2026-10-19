/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FullTateModule
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Compatible actual torsion families on a multiplicative set of indices

Restricting positive indices to a submonoid preserves products and therefore
the actual multiplication transitions. Each coordinate is an actual torsion
point, and the topology is the subspace topology of discrete torsion levels.
-/

namespace ProCGroups

universe u

variable (M : Type u) [AddCommGroup M] (S : Submonoid ℕ+)

/-- The actual compatible families over a multiplicative set of positive indices. -/
def restrictedCompatibleTorsionFamilies : AddSubgroup (∀ n : S, torsionLevel M n.1) where
  carrier := {x | ∀ n m : S, torsionTransition M n.1 m.1 (x (n * m)) = x n}
  zero_mem' := fun n m => (torsionTransition M n.1 m.1).map_zero
  add_mem' := by
    intro x y hx hy n m
    change torsionTransition M n.1 m.1 (x (n * m) + y (n * m)) = x n + y n
    rw [map_add, hx n m, hy n m]
  neg_mem' := by
    intro x hx n m
    change torsionTransition M n.1 m.1 (-x (n * m)) = -x n
    rw [map_neg, hx n m]

/-- The Tate module formed from the actual torsion levels with indices in `S`. -/
def RestrictedTateModule : Type u := ↥(restrictedCompatibleTorsionFamilies M S)

namespace RestrictedTateModule

instance : AddCommGroup (RestrictedTateModule M S) :=
  inferInstanceAs (AddCommGroup ↥(restrictedCompatibleTorsionFamilies M S))

/-- Projection to the actual torsion group at an allowed index. -/
def projection (n : S) : RestrictedTateModule M S →+ torsionLevel M n.1 where
  toFun x := x.1 n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation in the original group of points. -/
def evaluation (n : S) : RestrictedTateModule M S →+ M :=
  (torsionLevel M n.1).subtype.comp (projection M S n)

variable {M S}

/-- Compatible families are equal if their actual points at every allowed index agree. -/
@[ext] theorem ext {x y : RestrictedTateModule M S}
    (h : ∀ n : S, evaluation M S n x = evaluation M S n y) : x = y := by
  apply Subtype.ext
  funext n
  exact Subtype.ext (h n)

/-- The defining transitions are multiplication in the original group. -/
theorem evaluation_compatible (x : RestrictedTateModule M S) (n m : S) :
    (m.1 : ℕ) • evaluation M S (n * m) x = evaluation M S n x :=
  congrArg (fun z : torsionLevel M n.1 => z.1) (x.2 n m)

/-- A restricted compatible torsion family with finite coordinate range is zero.
A finite product of indices in `S` kills its entire coordinate range. -/
theorem eq_zero_of_finite_range (x : RestrictedTateModule M S)
    (hfinite : (Set.range (fun n : S => evaluation M S n x)).Finite) : x = 0 := by
  let R : Set M := Set.range (fun n : S => evaluation M S n x)
  have hkill : ∃ m : S, ∀ y ∈ R, (m.1 : ℕ) • y = 0 := by
    refine Set.Finite.induction_on_subset
      (motive := fun t _ => ∃ m : S, ∀ y ∈ t, (m.1 : ℕ) • y = 0)
      R hfinite ?_ ?_
    · exact ⟨1, fun _ h => False.elim h⟩
    · intro a t ha _ _ ih
      obtain ⟨n, rfl⟩ := ha
      obtain ⟨m, hm⟩ := ih
      refine ⟨n * m, ?_⟩
      intro y hy
      rcases Set.mem_insert_iff.mp hy with h | hy
      · subst y
        have hn : (n.1 : ℕ) • evaluation M S n x = 0 :=
          (projection M S n x).property
        change ((n.1 : ℕ) * (m.1 : ℕ)) • evaluation M S n x = 0
        rw [Nat.mul_comm, mul_smul, hn, nsmul_zero]
      · change ((n.1 : ℕ) * (m.1 : ℕ)) • y = 0
        rw [mul_smul, hm y hy, nsmul_zero]
  obtain ⟨m, hm⟩ := hkill
  apply ext
  intro n
  rw [map_zero]
  exact (evaluation_compatible x n m).symm.trans (hm _ ⟨n * m, rfl⟩)

variable (M S)

local instance (n : ℕ+) : TopologicalSpace (torsionLevel M n) :=
  FullTateModule.torsionLevelTopology M n

local instance (n : ℕ+) : DiscreteTopology (torsionLevel M n) := ⟨rfl⟩

instance : TopologicalSpace (RestrictedTateModule M S) :=
  inferInstanceAs (TopologicalSpace ↥(restrictedCompatibleTorsionFamilies M S))

instance : IsTopologicalAddGroup (RestrictedTateModule M S) :=
  inferInstanceAs (IsTopologicalAddGroup ↥(restrictedCompatibleTorsionFamilies M S))

instance : T2Space (RestrictedTateModule M S) :=
  inferInstanceAs (T2Space ↥(restrictedCompatibleTorsionFamilies M S))

instance : TotallyDisconnectedSpace (RestrictedTateModule M S) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(restrictedCompatibleTorsionFamilies M S))

/-- Every coordinate projection is continuous for the discrete torsion topology. -/
theorem continuous_projection (n : S) : Continuous (projection M S n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Compatibility is a closed condition in the product of the actual discrete levels. -/
theorem isClosed_restrictedCompatibleTorsionFamilies :
    IsClosed (restrictedCompatibleTorsionFamilies M S :
      Set (∀ n : S, torsionLevel M n.1)) := by
  change IsClosed {x : ∀ n : S, torsionLevel M n.1 |
    ∀ n m : S, torsionTransition M n.1 m.1 (x (n * m)) = x n}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun m => ?_
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (torsionTransition M n.1 m.1)).comp
      (continuous_apply (n * m))) (continuous_apply n)

instance [∀ n : S, Finite (torsionLevel M n.1)] : CompactSpace (RestrictedTateModule M S) :=
  (isClosed_restrictedCompatibleTorsionFamilies M S).isClosedEmbedding_subtypeVal.compactSpace

end RestrictedTateModule
end ProCGroups
