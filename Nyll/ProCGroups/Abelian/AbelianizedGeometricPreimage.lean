/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Geometric inverse images of full abelianized subgroups

The original abelianization map defines the inverse image inside the
specified geometric subgroup. Equality of abelianized images under the
same ambient isomorphism gives equality of these actual inverse images.
No equality of the original subgroups is assumed.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

universe u v

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- The inverse image of an abelianized subgroup in the original geometric
subgroup, viewed inside the original ambient group. -/
def abelianizedGeometricPreimage (A I : Subgroup P) : Subgroup P :=
  ((I.map (TopologicalAbelianization.mk P)).comap (TopologicalAbelianization.mk P)) ⊓ A

/-- Restricting the original quotient map to the geometric subgroup and
then returning its inverse image to the ambient group gives the same subgroup. -/
theorem abelianizedGeometricPreimage_eq_restricted (A I : Subgroup P) :
    abelianizedGeometricPreimage A I =
      (((I.map (TopologicalAbelianization.mk P)).comap
        ((TopologicalAbelianization.mk P).comp A.subtype)).map A.subtype) := by
  change _ = (((I.map (TopologicalAbelianization.mk P)).comap
    (TopologicalAbelianization.mk P)).subgroupOf A).map A.subtype
  exact (Subgroup.subgroupOf_map_subtype _ A).symm

/-- Returning the geometric inverse image to the same abelianization
recovers the original image whenever the subgroup is geometric. -/
theorem abelianizedGeometricPreimage_map_mk
    (A I : Subgroup P) (hI : I ≤ A) :
    (abelianizedGeometricPreimage A I).map (TopologicalAbelianization.mk P) =
      I.map (TopologicalAbelianization.mk P) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyI, _⟩, rfl⟩
    exact hyI
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, ⟨⟨y, hy, rfl⟩, hI hy⟩, rfl⟩

/-- Abelianizing an actual subgroup commutes with transporting it through
the same original continuous isomorphism. -/
theorem abelianizedSubgroup_map_congr
    {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (I : Subgroup P) (e : P ≃ₜ* Q) :
    (I.map (TopologicalAbelianization.mk P)).map
        (TopologicalAbelianization.congr e).toMonoidHom =
      (I.map e.toMonoidHom).map (TopologicalAbelianization.mk Q) := by
  have h : (TopologicalAbelianization.congr e).toMonoidHom.comp
      (TopologicalAbelianization.mk P) =
      (TopologicalAbelianization.mk Q).comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact TopologicalAbelianization.congr_apply_mk e x
  rw [Subgroup.map_map, Subgroup.map_map, h]

/-- Matching the actual abelianized inertia directions under the same
ambient isomorphism matches their geometric inverse images. -/
theorem abelianizedGeometricPreimage_map_of_image_eq
    {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (A I : Subgroup P) (B J : Subgroup Q) (e : P ≃ₜ* Q)
    (hA : A.map e.toMonoidHom = B)
    (hI : (I.map (TopologicalAbelianization.mk P)).map
      (TopologicalAbelianization.congr e).toMonoidHom =
        J.map (TopologicalAbelianization.mk Q)) :
    (abelianizedGeometricPreimage A I).map e.toMonoidHom =
      abelianizedGeometricPreimage B J := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyI, hyA⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change TopologicalAbelianization.mk Q (e y) ∈ J.map (TopologicalAbelianization.mk Q)
      rw [← hI]
      exact ⟨TopologicalAbelianization.mk P y, hyI,
        TopologicalAbelianization.congr_apply_mk e y⟩
    · rw [← hA]
      exact ⟨y, hyA, rfl⟩
  · rintro ⟨hxJ, hxB⟩
    rw [← hA] at hxB
    obtain ⟨y, hyA, rfl⟩ := hxB
    refine ⟨y, ⟨?_, hyA⟩, rfl⟩
    change TopologicalAbelianization.mk Q (e y) ∈ J.map (TopologicalAbelianization.mk Q) at hxJ
    rw [← hI] at hxJ
    obtain ⟨b, hb, hby⟩ := hxJ
    have hb' : b = TopologicalAbelianization.mk P y :=
      (TopologicalAbelianization.congr e).injective
        (hby.trans (TopologicalAbelianization.congr_apply_mk e y).symm)
    change TopologicalAbelianization.mk P y ∈ I.map (TopologicalAbelianization.mk P)
    exact hb' ▸ hb

end ProCGroups.Abelian
