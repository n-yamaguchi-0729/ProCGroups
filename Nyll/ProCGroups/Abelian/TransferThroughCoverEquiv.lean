/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.FiniteTransferSquare

/-!
# Original transfer through actual covering-group equivalences

An actual surjective square of original ambient and covering groups
retains the original transfer after identifying the covering groups
with their actual finite-index subgroups. The proof reduces to the
proved ordinary transfer character square on the same representatives.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

variable {G P G' P' : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [Group P'] [TopologicalSpace P'] [IsTopologicalGroup P']

/-- Original transfer commutes with an actual covering quotient square.
The two equivalences are the original covering-subgroup identifications,
and the square is on their original ambient group elements. -/
theorem openNormalTransfer_through_cover_equivalences
    (f : G →ₜ* P) (hf : Function.Surjective f)
    (N : OpenNormalSubgroup G) (M : OpenNormalSubgroup P)
    [Finite (G ⧸ N.toSubgroup)] [Finite (P ⧸ M.toSubgroup)]
    (hker : f.toMonoidHom.ker ≤ N.toSubgroup)
    (eG : G' ≃ₜ* N.toSubgroup) (eP : P' ≃ₜ* M.toSubgroup)
    (g : G' →ₜ* P') (hg : Function.Surjective g)
    (hsquare : ∀ x : G', (eP (g x)).val = f (eG x).val)
    (z : TopologicalAbelianization G) :
    TopologicalAbelianization.map g
        ((TopologicalAbelianization.congr eG).symm
          (openNormalTransferTopologicalAbelianization N z)) =
      (TopologicalAbelianization.congr eP).symm
        (openNormalTransferTopologicalAbelianization M (TopologicalAbelianization.map f z)) := by
  have hNindex : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hMindex : M.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let r : N.toSubgroup →ₜ* P' :=
    g.comp (ContinuousMonoidHom.toContinuousMonoidHom eG.symm)
  have hr : Function.Surjective r := hg.comp eG.symm.surjective
  have hsq (n : N.toSubgroup) : (eP (r n)).val = f n.val := by
    exact (hsquare (eG.symm n)).trans
      (congrArg (fun x : N.toSubgroup => f x.val) (eG.apply_symm_apply n))
  have hcomp (a : TopologicalAbelianization N.toSubgroup) :
      TopologicalAbelianization.map g ((TopologicalAbelianization.congr eG).symm a) =
        TopologicalAbelianization.map r a := by
    change TopologicalAbelianization.map g
      (TopologicalAbelianization.map
        (ContinuousMonoidHom.toContinuousMonoidHom eG.symm) a) = _
    exact (DFunLike.congr_fun (TopologicalAbelianization.map_comp g
      (ContinuousMonoidHom.toContinuousMonoidHom eG.symm)) a).symm
  rw [hcomp]
  obtain ⟨x, rfl⟩ := TopologicalAbelianization.surjective_mk G z
  rw [TopologicalAbelianization.map_apply_mk]
  change TopologicalAbelianization.lift ((TopologicalAbelianization.mkₜ P').comp r)
      (openNormalTransferTopologicalAbelianization N (TopologicalAbelianization.mk G x)) =
    TopologicalAbelianization.lift ((TopologicalAbelianization.mkₜ P').comp
      (ContinuousMonoidHom.toContinuousMonoidHom eP.symm))
      (openNormalTransferTopologicalAbelianization M (TopologicalAbelianization.mk P (f x)))
  rw [lift_openNormalTransfer_apply_mk, lift_openNormalTransfer_apply_mk]
  exact ClassFormation.transfer_character_through_range_equiv f.toMonoidHom hf
    N.toSubgroup hker M.toSubgroup r.toMonoidHom hr eP.toMulEquiv hsq
    (TopologicalAbelianization.mk P') x

end ProCGroups.FiniteStepSolvableQuotients
