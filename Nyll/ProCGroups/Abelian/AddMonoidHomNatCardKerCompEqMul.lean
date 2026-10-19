/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Add Monoid Hom nat Card ker comp eq mul of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective

namespace P2mKerMul

variable {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]

/-- The map from the kernel of a composite to the kernel of its second map. -/
def kerMap (f : A →+ B) (g : B →+ C) : (g.comp f).ker →+ g.ker :=
  (f.domRestrict (g.comp f).ker).codRestrict g.ker fun x => by
    rw [AddMonoidHom.domRestrict_apply, AddMonoidHom.mem_ker]
    have hx := x.2
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at hx

@[scoped simp] theorem kerMap_apply (f : A →+ B) (g : B →+ C) (x : (g.comp f).ker) :
    (kerMap f g x : B) = f x := rfl

theorem kerMap_surjective (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Function.Surjective (kerMap f g) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ (g.comp f).ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
    rwa [AddMonoidHom.mem_ker] at hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem ker_le (f : A →+ B) (g : B →+ C) : f.ker ≤ (g.comp f).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]

theorem ker_kerMap (f : A →+ B) (g : B →+ C) :
    (kerMap f g).ker = f.ker.addSubgroupOf (g.comp f).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker,
    ← kerMap_apply]
  exact ⟨fun h => by rw [h, AddSubgroup.coe_zero], fun h => Subtype.ext h⟩

theorem natCard_ker_comp (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by
  calc Nat.card (g.comp f).ker
      = Nat.card ((g.comp f).ker ⧸ (kerMap f g).ker) * Nat.card (kerMap f g).ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card g.ker * Nat.card f.ker := by
        rw [Nat.card_congr
            (QuotientAddGroup.quotientKerEquivOfSurjective _ (kerMap_surjective f g hf)).toEquiv,
          ker_kerMap, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (ker_le f g)).toEquiv]

end P2mKerMul

theorem _root_.AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective {A B C : Type*} [AddGroup A]
  [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker :=
  P2mKerMul.natCard_ker_comp f g hf
end AlgebraicCurves.Foundations.Algebra.Proofs.AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective
end ProofImplementation
