/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.ProCGroups.Abelian.AddCommGroupBasisSmulEq

/-!
# Add Comm Group nonempty basis zmod pow of card torsion By
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy

namespace P2mLwFree

open Module Submodule Function

variable {M : Type*} [AddCommGroup M]

theorem nsmul_coe_torsionBy (k : ℕ) (x : torsionBy ℤ M ((k : ℕ) : ℤ)) : k • (x : M) = 0 := by
  have := (mem_torsionBy_iff _ _).1 x.2
  rwa [natCast_zsmul] at this

/-- The action of ZMod k on the subgroup annihilated by multiplication by k. -/
@[reducible] def modInst (k : ℕ) : Module (ZMod k) (torsionBy ℤ M ((k : ℕ) : ℤ)) :=
  AddCommGroup.zmodModule fun x => Subtype.ext (by
    rw [Submodule.coe_smul_of_tower, Submodule.coe_zero]
    exact nsmul_coe_torsionBy k x)

attribute [local instance] modInst

theorem mem_range_subtype_iff (k : ℕ) (x : M) :
    x ∈ ((torsionBy ℤ M ((k : ℕ) : ℤ)).subtype.toAddMonoidHom).range ↔ ((k : ℕ) : ℤ) • x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_torsionBy_iff _ _).1 v.2
  · intro hx
    exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hx⟩, rfl⟩

theorem nonempty_basis_of_subsingleton {R : Type*} [Semiring R] [Subsingleton R] {W : Type*}
    [AddCommMonoid W] [Module R W] [Subsingleton W] (r : ℕ) : Nonempty (Basis (Fin r) R W) :=
  ⟨Basis.ofEquivFun (LinearEquiv.ofSubsingleton W (Fin r → R))⟩

theorem levelZero (ℓ r : ℕ) :
    Nonempty (Basis (Fin r) (ZMod (ℓ ^ 0)) (torsionBy ℤ M ((ℓ ^ 0 : ℕ) : ℤ))) := by
  have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero ℓ)
  have : Subsingleton (torsionBy ℤ M ((ℓ ^ 0 : ℕ) : ℤ)) := ⟨fun x y => Subtype.ext (by
    have hx : (1 : ℕ) • (x : M) = 0 := by simpa only [pow_zero] using nsmul_coe_torsionBy (ℓ ^ 0) x
    have hy : (1 : ℕ) • (y : M) = 0 := by simpa only [pow_zero] using nsmul_coe_torsionBy (ℓ ^ 0) y
    rw [one_smul] at hx hy
    rw [hx, hy])⟩
  exact nonempty_basis_of_subsingleton r

theorem nonempty_basis_torsionBy (ℓ : ℕ) [Fact ℓ.Prime] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r) :
    ∀ j ≤ m, Nonempty (Basis (Fin r) (ZMod (ℓ ^ j)) (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ))) := by
  intro j
  induction j with
  | zero => exact fun _ => levelZero ℓ r
  | succ j ih =>
    intro hj
    obtain ⟨c⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨c', -⟩ := AddCommGroup.exists_basis_smul_eq_of_card_torsionBy ℓ r j
      (fun i hi => hcard i (hi.trans hj))
      (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)).subtype.toAddMonoidHom Subtype.val_injective
      (mem_range_subtype_iff (ℓ ^ j))
      (torsionBy ℤ M ((ℓ ^ (j + 1) : ℕ) : ℤ)).subtype.toAddMonoidHom Subtype.val_injective
      (mem_range_subtype_iff (ℓ ^ (j + 1))) c
    exact ⟨c'⟩

theorem nonempty_basis_of_carrier (n : ℕ) {ι' : Type*} (b : Basis ι' (ZMod n) (torsionBy ℤ M ((n :
  ℕ) : ℤ)))
    {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0) :
    Nonempty (Basis ι' (ZMod n) V) := by
  let f : V →+ torsionBy ℤ M ((n : ℕ) : ℤ) :=
    ι.codRestrict (torsionBy ℤ M ((n : ℕ) : ℤ)) fun v =>
      (mem_torsionBy_iff _ _).2 ((hιr _).1 ⟨v, rfl⟩)
  have hf : Bijective f := by
    refine ⟨fun v w h => hι (Subtype.ext_iff.1 h), fun x => ?_⟩
    obtain ⟨v, hv⟩ := (hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
    exact ⟨v, Subtype.ext hv⟩
  let e : V ≃ₗ[ZMod n] torsionBy ℤ M ((n : ℕ) : ℤ) :=
    LinearEquiv.ofBijective (f.toZModLinearMap n) hf
  exact ⟨b.map e.symm⟩

end P2mLwFree

theorem _root_.AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) := by
  let := P2mLwFree.modInst (M := M) (ℓ ^ m)
  obtain ⟨b⟩ := P2mLwFree.nonempty_basis_torsionBy ℓ r m hcard m le_rfl
  exact P2mLwFree.nonempty_basis_of_carrier (ℓ ^ m) b ι hι hιr
end AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
