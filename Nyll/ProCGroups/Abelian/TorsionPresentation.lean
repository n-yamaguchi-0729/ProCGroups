/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Presentations of a torsion subgroup

The presentation records the specified injective additive map and its exact
range. No finiteness, primality or nonzero-exponent assumption is needed here.
-/

@[expose] public section

namespace ProCGroups.Abelian

open Module Submodule Function

/-- A presentation of the subgroup killed by `n` as the image of an injective additive map. -/
structure TorsionPresentation (M : Type*) [AddCommGroup M] (n : ℕ)
    (V : Type*) [AddCommGroup V] where
  /-- The additive map presenting the torsion subgroup. -/
  ι : V →+ M
  /-- Injectivity of the presentation map. -/
  hι : Injective ι
  /-- The image consists precisely of the elements killed by `n`. -/
  hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0

namespace TorsionPresentation

variable {M : Type*} [AddCommGroup M] {n : ℕ} {V : Type*} [AddCommGroup V]

theorem nsmul_ι (P : TorsionPresentation M n V) (v : V) : n • P.ι v = 0 := by
  have := (P.hιr (P.ι v)).1 ⟨v, rfl⟩
  rwa [natCast_zsmul] at this

theorem nsmul_self (P : TorsionPresentation M n V) (v : V) : n • v = 0 :=
  P.hι (by rw [map_nsmul, P.nsmul_ι, map_zero])

theorem exists_eq (P : TorsionPresentation M n V) {x : M} (hx : n • x = 0) : ∃ v, P.ι v = x := by
  obtain ⟨v, hv⟩ := (P.hιr x).2 (by rwa [natCast_zsmul])
  exact ⟨v, hv⟩

theorem mem_torsionBy (P : TorsionPresentation M n V) (v : V) :
    P.ι v ∈ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).2 ((P.hιr _).1 ⟨v, rfl⟩)

/-- The equivalence between the presented group and the subgroup killed by `n`. -/
noncomputable def equiv (P : TorsionPresentation M n V) : V ≃ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun v => ⟨P.ι v, P.mem_torsionBy v⟩)
    ⟨fun v w h => P.hι (Subtype.ext_iff.1 h), fun x => by
      obtain ⟨v, hv⟩ := (P.hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
      exact ⟨v, Subtype.ext hv⟩⟩

theorem natCard_eq (P : TorsionPresentation M n V) :
    Nat.card V = Nat.card (torsionBy ℤ M ((n : ℕ) : ℤ)) :=
  Nat.card_congr P.equiv

variable (M) in
/-- The presentation of the torsion subgroup by its inclusion in the ambient group. -/
def self (n : ℕ) : TorsionPresentation M n (torsionBy ℤ M ((n : ℕ) : ℤ)) where
  ι := (torsionBy ℤ M ((n : ℕ) : ℤ)).subtype.toAddMonoidHom
  hι := Subtype.val_injective
  hιr x := by
    constructor
    · rintro ⟨v, rfl⟩
      exact (mem_torsionBy_iff _ _).1 v.2
    · intro hx
      exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hx⟩, rfl⟩

end TorsionPresentation

end ProCGroups.Abelian
