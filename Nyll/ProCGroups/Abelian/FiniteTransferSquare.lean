/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalTransferComparison

/-!
# Transfer through an actual finite quotient square

An original subgroup quotient is often represented by an isomorphic copy
of its image in the ambient quotient. The transfer character is unchanged
by this representation. This lemma keeps that exact image identification
separate from the native Galois and reciprocity comparisons.
-/

@[expose] public section

noncomputable section

namespace ClassFormation

variable {P Q R A : Type*} [Group P] [Group Q] [Group R] [CommGroup A]

/-- Transporting a character across equality of finite-index subgroups
does not change its transfer to the ambient group. -/
theorem transfer_character_congr_subgroup
    (H J : Subgroup Q) (h : H = J) [H.FiniteIndex] [J.FiniteIndex]
    (χ : J →* A) :
    MonoidHom.transfer (χ.comp (MulEquiv.subgroupCongr h).toMonoidHom) =
      MonoidHom.transfer χ := by
  subst J
  rfl

/-- A surjective quotient square computes transfer using the original
equivalence from the relative quotient to its actual ambient image. -/
theorem transfer_character_through_range_equiv
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) [H.FiniteIndex] (hker : f.ker ≤ H)
    (J : Subgroup Q) [J.FiniteIndex]
    (r : H →* R) (hr : Function.Surjective r) (e : R ≃* J)
    (hsquare : ∀ h : H, (e (r h)).val = f h.val)
    (χ : R →* A) (p : P) :
    MonoidHom.transfer (χ.comp r) p =
      MonoidHom.transfer (χ.comp e.symm.toMonoidHom) (f p) := by
  have hmap : H.map f = J := by
    apply Subgroup.ext
    intro q
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [← hsquare ⟨h, hh⟩]
      exact (e (r ⟨h, hh⟩)).property
    · intro hq
      obtain ⟨h, hh⟩ := hr (e.symm ⟨q, hq⟩)
      refine ⟨h.val, h.property, ?_⟩
      rw [← hsquare h, hh, e.apply_symm_apply]
  have himage : (H.map f).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective (H := H) (f := f) hf
  let c := MulEquiv.subgroupCongr hmap
  let ψ : J →* A := χ.comp e.symm.toMonoidHom
  let ψmap : H.map f →* A := ψ.comp c.toMonoidHom
  have hcomp : ψmap.comp (f.subgroupMap H) = χ.comp r := by
    apply MonoidHom.ext
    intro h
    apply congrArg χ
    apply e.injective
    change e (e.symm (c (f.subgroupMap H h))) = e (r h)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact (hsquare h).symm
  have hnat := transfer_character_natural_of_surjective f hf H hker ψmap p
  rw [hcomp] at hnat
  calc
    MonoidHom.transfer (χ.comp r) p = MonoidHom.transfer ψmap (f p) := hnat
    _ = MonoidHom.transfer ψ (f p) :=
      congrArg (fun θ : Q →* A => θ (f p))
        (transfer_character_congr_subgroup (H.map f) J hmap ψ)

end ClassFormation
