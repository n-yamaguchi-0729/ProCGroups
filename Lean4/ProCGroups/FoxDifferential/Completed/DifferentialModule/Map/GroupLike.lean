import ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Limit

/-!
# Fox differential: completed — differential module — map — group like

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMap_of`
  The completed prime-power group-algebra map sends the group-like element of `g` to the group-like
  element of `ψ g`.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (0 < ℓ)] in
/--
The completed prime-power group-algebra map sends the group-like element of `g` to the group-like
element of `ψ g`.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_of
    (ψ : ContinuousMonoidHom G H) (g : G) :
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g))
  rw [primePowerCompletedGroupAlgebraProjection_map,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraMapStage_of,
    primePowerCompletedGroupAlgebraProjection_of]
  rfl


end

end FoxDifferential
