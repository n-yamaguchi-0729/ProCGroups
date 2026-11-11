/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Mathlib.Algebra.Group.End

/-!
# Marked unramified subgroups determine their abelian values

On a subgroup with trivial intersection with the arithmetic kernel, the
original arithmetic label is injective. Two marked group isomorphisms
whose images of that subgroup are conjugate therefore agree on every
individual element after abelianization. This retains the element and its
arithmetic normalization, rather than only the subgroup image.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

section Groups

variable {P Q Γ : Type*} [Group P] [Group Q] [CommGroup Γ]
  (π : P →* Γ) (π' : Q →* Γ) (e f : P ≃* Q)
  (he : ∀ x, π' (e x) = π x) (hf : ∀ x, π' (f x) = π x)

/-- The original arithmetic label is injective on every subgroup whose
intersection with its original kernel is trivial. -/
theorem injective_label_on_subgroup (D : Subgroup P) (hD : D ⊓ π.ker = ⊥)
    {x y : P} (hx : x ∈ D) (hy : y ∈ D) (hxy : π x = π y) : x = y := by
  have hmem : x / y ∈ D ⊓ π.ker :=
    ⟨D.div_mem hx hy, by
      change π (x / y) = 1
      rw [map_div, hxy, div_self']⟩
  rw [hD] at hmem
  exact div_eq_one.mp (Subgroup.mem_bot.mp hmem)

include he hf in
/-- The same arithmetic labels force the conjugator of unramified
subgroups to intertwine every original element of the subgroup. -/
theorem marked_conjugate_subgroup_apply
    (D : Subgroup P) (hD : D ⊓ π.ker = ⊥) (b : Q)
    (hconj : (D.map e.toMonoidHom).map (MulAut.conj b).toMonoidHom =
      D.map f.toMonoidHom) (x : P) (hx : x ∈ D) :
    b * e x * b⁻¹ = f x := by
  have hmem : b * e x * b⁻¹ ∈ D.map f.toMonoidHom := by
    rw [← hconj]
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have hlabel : π y = π x := by
    calc
      π y = π' (f y) := (hf y).symm
      _ = π' (b * e x * b⁻¹) := congrArg π' hyx
      _ = π' (e x) := by
        rw [map_mul, map_mul, map_inv, mul_comm (π' b) (π' (e x)),
          mul_assoc, mul_inv_cancel, mul_one]
      _ = π x := he x
  have hy_eq := injective_label_on_subgroup π D hD hy hx hlabel
  exact hyx.symm.trans (congrArg f hy_eq)

end Groups

section Abelianization

variable {P Q Γ : Type*} [Group P] [Group Q] [CommGroup Γ]
  [TopologicalSpace Q] [IsTopologicalGroup Q]
  (π : P →* Γ) (π' : Q →* Γ) (e f : P ≃* Q)
  (he : ∀ x, π' (e x) = π x) (hf : ∀ x, π' (f x) = π x)

include he hf in
/-- Conjugate images of an original unramified subgroup have the same
individual values under the full arithmetic abelianizations. -/
theorem abelianized_marked_equiv_eq_of_conjugate_subgroup
    (D : Subgroup P) (hD : D ⊓ π.ker = ⊥)
    (hconj : ∃ b : Q,
      (D.map e.toMonoidHom).map (MulAut.conj b).toMonoidHom =
        D.map f.toMonoidHom) (x : P) (hx : x ∈ D) :
    TopologicalAbelianization.mk Q (e x) = TopologicalAbelianization.mk Q (f x) := by
  obtain ⟨b, hb⟩ := hconj
  have h := marked_conjugate_subgroup_apply π π' e f he hf D hD b hb x hx
  rw [← h, map_mul, map_mul, map_inv,
    mul_comm (TopologicalAbelianization.mk Q b) (TopologicalAbelianization.mk Q (e x)),
    mul_assoc, mul_inv_cancel, mul_one]

end Abelianization

end ProCGroups.Abelian
