/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_card_torsion_mul_of_divisible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# card torsion mul of divisible
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.card_torsion_mul_of_divisible

open Function

theorem _root_.card_torsion_mul_of_divisible
    {A : Type*} [AddCommGroup A]
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ x : A, ∃ y : A, m • y = x)
    (a b : ℕ) (ha : a ≠ 0)
    (hfa : Finite {x : A // a • x = 0}) (hfb : Finite {x : A // b • x = 0}) :
    Finite {x : A // (a * b) • x = 0} ∧
      Nat.card {x : A // (a * b) • x = 0} =
        Nat.card {x : A // a • x = 0} * Nat.card {x : A // b • x = 0} := by
  let T : ℕ → AddSubgroup A := fun n => (zsmulAddGroupHom (n : ℤ)).ker
  have hT : ∀ n (x : A), x ∈ T n ↔ n • x = 0 := fun n x => by
    simp only [T, AddMonoidHom.mem_ker, zsmulAddGroupHom_apply, natCast_zsmul]
  have eT : ∀ n, {x : A // n • x = 0} ≃ T n := fun n =>
    Equiv.subtypeEquivRight fun x => (hT n x).symm
  let φ : T (a * b) →+ T b :=
    { toFun := fun x => ⟨a • (x : A), by
        rw [hT, ← mul_smul, mul_comm]; exact (hT (a*b) _).mp x.2⟩
      map_zero' := Subtype.ext (smul_zero a)
      map_add' := fun x y => by
        simp only [AddSubgroup.coe_add, smul_add]; rfl }
  have hφsurj : Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hdiv a ha y
    refine ⟨⟨z, ?_⟩, ?_⟩
    · rw [hT, mul_comm, mul_smul, hz]; exact (hT b y).mp hy
    · exact Subtype.ext hz
  have hmem_ker : ∀ x : T (a * b), x ∈ φ.ker ↔ a • (x : A) = 0 := fun x => by
    simp only [AddMonoidHom.mem_ker, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddSubgroup.mk_eq_zero]
  let hker : (φ.ker : Type _) ≃ T a :=
    { toFun := fun x => ⟨(x : T (a * b)), (hT a _).mpr ((hmem_ker _).mp x.2)⟩
      invFun := fun y => ⟨⟨(y : A), (hT (a*b) _).mpr (by
          rw [mul_comm, mul_smul, (hT a _).mp y.2, smul_zero])⟩,
        (hmem_ker _).mpr ((hT a _).mp y.2)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  have hcard : Nat.card (T (a * b)) = Nat.card (T a) * Nat.card (T b) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv,
      Nat.card_congr hker, mul_comm]
  have hfa' : Finite (T a) := (eT a).finite_iff.mp hfa
  have hfb' : Finite (T b) := (eT b).finite_iff.mp hfb
  have : (0 : A) ∈ T a := (hT a 0).mpr (smul_zero a)
  have : (0 : A) ∈ T b := (hT b 0).mpr (smul_zero b)
  have hpos : 0 < Nat.card (T (a * b)) := by
    rw [hcard]
    exact Nat.mul_pos Nat.card_pos Nat.card_pos
  have hfab' : Finite (T (a * b)) := (Nat.card_pos_iff.mp hpos).2
  refine ⟨(eT (a*b)).finite_iff.mpr hfab', ?_⟩
  rw [Nat.card_congr (eT (a*b)), Nat.card_congr (eT a), Nat.card_congr (eT b), hcard]
end AlgebraicCurves.Foundations.Algebra.Proofs.card_torsion_mul_of_divisible
end ProofImplementation
