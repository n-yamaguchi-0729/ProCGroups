/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Submodule nat Card torsion By quotient eq pow finrank
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Submodule_natCard_torsionBy_quotient_eq_pow_finrank

namespace Submodule
open _root_.Submodule
namespace LatticeQuotientTorsion
open _root_.Submodule

open _root_.Submodule

universe u v

variable {K : Type u} [DivisionRing K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The additive map given by multiplication by the inverse of the natural-number scalar. -/
noncomputable def divN (n : ℕ) : V →+ V :=
  DistribSMul.toAddMonoidHom V ((n : K)⁻¹)

theorem natCast_smul_divN {n : ℕ} (hn : n ≠ 0) (v : V) :
    (n : ℤ) • divN (K := K) n v = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hK, one_smul]

theorem divN_natCast_smul {n : ℕ} (hn : n ≠ 0) (v : V) :
    divN (K := K) n ((n : ℤ) • v) = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hK, one_smul]

variable (L : Submodule ℤ V)

/-- The map sending a lattice vector divided by the scalar to its torsion class in the quotient. -/
noncomputable def latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    L →ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) where
  toFun w := ⟨Submodule.Quotient.mk (divN (K := K) n (w : V)), by
    rw [mem_torsionBy_iff]
    change (Submodule.Quotient.mk ((n : ℤ) • divN (K := K) n (w : V)) : V ⧸ L) = 0
    rw [natCast_smul_divN (K := K) hn]
    exact (Submodule.Quotient.mk_eq_zero L).mpr w.2⟩
  map_add' a b := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((a + b : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (divN (K := K) n (a : V))
        + Submodule.Quotient.mk (divN (K := K) n (b : V))
    rw [Submodule.coe_add, map_add, Submodule.Quotient.mk_add]
  map_smul' m a := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((m • a : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (m • divN (K := K) n (a : V))
    rw [Submodule.coe_smul, map_zsmul]

theorem coe_latticeDivQuot {n : ℕ} (hn : n ≠ 0) (w : L) :
    ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
      = Submodule.Quotient.mk (divN (K := K) n (w : V)) := rfl

theorem latticeDivQuot_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (latticeDivQuot (K := K) L hn) := by
  rintro ⟨x, hx⟩
  rw [mem_torsionBy_iff] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  have hvL : (n : ℤ) • v ∈ L := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvL⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • v)) : V ⧸ L)
      = Submodule.Quotient.mk v
  rw [divN_natCast_smul (K := K) hn]

theorem ker_latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    LinearMap.ker (latticeDivQuot (K := K) L hn)
      = LinearMap.range (LinearMap.lsmul ℤ L (n : ℤ)) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hker
    have hcoe : ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
        = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, Submodule.Quotient.mk_eq_zero] at hcoe
    refine ⟨⟨divN (K := K) n (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    change (n : ℤ) • divN (K := K) n (w : V) = (w : V)
    exact natCast_smul_divN (K := K) hn (w : V)
  · rintro ⟨μ, rfl⟩
    apply Subtype.ext
    rw [coe_latticeDivQuot, LinearMap.lsmul_apply]
    change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • (μ : V))) : V ⧸ L) = 0
    rw [divN_natCast_smul (K := K) hn, Submodule.Quotient.mk_eq_zero]
    exact μ.2

/-- The equivalence between the lattice modulo the scalar and the scalar-torsion subgroup of its
quotient. -/
noncomputable def latticeQuotTorsionEquiv {n : ℕ} (hn : n ≠ 0) :
    ModN L n ≃ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeDivQuot (K := K) L hn).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (latticeDivQuot_surjective (K := K) L hn))

end Submodule.LatticeQuotientTorsion

theorem _root_.Submodule.natCard_torsionBy_quotient_eq_pow_finrank
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by
  have : NeZero n := ⟨hn⟩
  rw [← Nat.card_congr
    (Submodule.LatticeQuotientTorsion.latticeQuotTorsionEquiv (K := K) L hn).toEquiv,
    ModN.natCard_eq]
end AlgebraicCurves.Foundations.Algebra.Proofs.Submodule_natCard_torsionBy_quotient_eq_pow_finrank
end ProofImplementation
