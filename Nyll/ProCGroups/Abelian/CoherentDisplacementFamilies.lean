/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.ConjugationDifferenceIntersection

/-!
# Coherence of full subgroup recovery through constant powers

Suppose the same ambient isomorphism matches a family of actual closed
subgroups modulo every positive-power conjugation displacement. If their
first displacement quotients distinguish the target indices, the choices
at every higher power are forced to have that same index: adding the first
displacement reduces each comparison to the first one.

The intersection theorem then recovers each entire original subgroup under
the given isomorphism. This algebraic step supplies coherence rather than
assuming a compatible family of target choices.
-/

@[expose] public section

noncomputable section

open scoped IsMulCommutative

namespace ProCGroups.Abelian

universe u v w w'

variable {P : Type u} {Q : Type v}
  [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
  [IsTopologicalGroup P] [IsTopologicalGroup Q]
  [CompactSpace P] [CompactSpace Q]
  [TotallyDisconnectedSpace P] [TotallyDisconnectedSpace Q] [T2Space Q]
  (A : Subgroup P) (B : Subgroup Q)
  [A.Normal] [B.Normal] [IsMulCommutative A] [IsMulCommutative B]
  (e : P ≃ₜ* Q) (hAB : A.map e.toMonoidHom = B)
  {ι : Type w} {κ : Type w'} (I : ι → Subgroup P) (J : κ → Subgroup Q)
  (hI : ∀ i, IsClosed (I i : Set P)) (hJ : ∀ j, IsClosed (J j : Set Q))
  (d : P)

include hAB hI hJ in
omit [IsTopologicalGroup P] [TotallyDisconnectedSpace P] in
/-- The target selected at the first displacement quotient is forced at
every positive power, and hence identifies the full original subgroup.
No prior choice of a coherent target function is used. -/
theorem exists_unique_map_closedSubgroup_of_displacement_families
    (hseparate : Function.Injective (fun j => J j ⊔ conjugationDifferenceImage B (e d)))
    (hmatch : ∀ (n : ℕ+) (i : ι), ∃ j : κ,
      (I i ⊔ conjugationDifferenceImage A (d ^ (n : ℕ))).map e.toMonoidHom =
        J j ⊔ conjugationDifferenceImage B ((e d) ^ (n : ℕ)))
    (i : ι) : ∃! j : κ, (I i).map e.toMonoidHom = J j := by
  obtain ⟨j, hj⟩ := hmatch 1 i
  change (I i ⊔ conjugationDifferenceImage A (d ^ 1)).map e.toMonoidHom =
    J j ⊔ conjugationDifferenceImage B ((e d) ^ 1) at hj
  rw [pow_one, pow_one] at hj
  have hcoherent (n : ℕ+) :
      (I i ⊔ conjugationDifferenceImage A (d ^ (n : ℕ))).map e.toMonoidHom =
        J j ⊔ conjugationDifferenceImage B ((e d) ^ (n : ℕ)) := by
    obtain ⟨l, hl⟩ := hmatch n i
    have hjoined := congrArg (fun H : Subgroup Q => H ⊔ conjugationDifferenceImage B (e d)) hl
    rw [Subgroup.map_sup, conjugationDifferenceImage_map A B e.toMulEquiv hAB,
      map_pow] at hjoined
    change ((I i).map e.toMonoidHom ⊔
      conjugationDifferenceImage B ((e d) ^ (n : ℕ))) ⊔
        conjugationDifferenceImage B (e d) =
      (J l ⊔ conjugationDifferenceImage B ((e d) ^ (n : ℕ))) ⊔
        conjugationDifferenceImage B (e d) at hjoined
    rw [sup_assoc,
      sup_eq_right.mpr (conjugationDifferenceImage_pow_le B (e d) (n : ℕ)),
      sup_assoc,
      sup_eq_right.mpr (conjugationDifferenceImage_pow_le B (e d) (n : ℕ))] at hjoined
    have hfirst : (I i).map e.toMonoidHom ⊔ conjugationDifferenceImage B (e d) =
        J j ⊔ conjugationDifferenceImage B (e d) := by
      rw [Subgroup.map_sup, conjugationDifferenceImage_map A B e.toMulEquiv hAB] at hj
      exact hj
    have hlj : l = j := hseparate (hjoined.symm.trans hfirst)
    exact hlj ▸ hl
  have hfull : (I i).map e.toMonoidHom = J j :=
    map_closedSubgroup_eq_of_sup_conjugationDifferenceImage_eq A B e hAB
      (I i) (J j) (hI i) (hJ j) d hcoherent
  refine ⟨j, hfull, ?_⟩
  intro l hl
  apply hseparate
  exact congrArg (fun H : Subgroup Q => H ⊔ conjugationDifferenceImage B (e d))
    (hl.symm.trans hfull)

end ProCGroups.Abelian
