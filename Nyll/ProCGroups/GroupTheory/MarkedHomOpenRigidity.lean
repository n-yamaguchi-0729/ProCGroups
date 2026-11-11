/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Profinite.OpenSubgroups
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Extending a marked homomorphism comparison from an open subgroup

The discrepancy between two marked maps centralizes the part of their
agreement subgroup also fixed by conjugation from the source. A positive
power of a chosen arithmetic lift lies in that open intersection. If such
lifts fix only the identity in the target kernel, the discrepancy vanishes.
-/

@[expose] public section

namespace ProCGroups

/-- Agreement on one open arithmetic subgroup determines marked homomorphisms
whenever all positive powers of the specified arithmetic label have no
nonidentity fixed elements in the target kernel. Neither map is assumed
injective or surjective. -/
theorem markedHoms_eq_of_agreeOnOpen_of_fixedKernelPowers
    {P Q Γ : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [Group Q] [Group Γ] (π : P →* Γ) (ρ : Q →* Γ)
    (e f : P →* Q) (he : ∀ x, ρ (e x) = π x) (hf : ∀ x, ρ (f x) = π x)
    (γ : Γ) (t : P) (ht : π t = γ)
    (hfixed : ∀ (n : ℕ), n ≠ 0 → ∀ d : Q, ρ d = γ ^ n →
      ∀ a : ρ.ker, MulAut.conjNormal d a = a → a = 1)
    (U : OpenSubgroup P) (hU : ∀ x : P, x ∈ U → e x = f x) : e = f := by
  apply MonoidHom.ext
  intro g
  let C : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj g).toMonoidHom
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  let V : OpenSubgroup P := U ⊓ U.comap C.toMonoidHom C.continuous_toFun
  obtain ⟨n, hn, htn⟩ := exists_pos_pow_mem_openSubgroup V t
  have htnU : t ^ n ∈ U := htn.1
  have hconjU : g * t ^ n * g⁻¹ ∈ U := htn.2
  let a : ρ.ker := ⟨(f g)⁻¹ * e g, by
    change ρ ((f g)⁻¹ * e g) = 1
    rw [map_mul, map_inv, he, hf, inv_mul_cancel]⟩
  have hcomm : e (t ^ n) * a.val = a.val * e (t ^ n) := by
    have h := hU (g * t ^ n * g⁻¹) hconjU
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      ← hU (t ^ n) htnU] at h
    have hmul := congrArg (fun x : Q => (f g)⁻¹ * x * e g) h
    change e (t ^ n) * ((f g)⁻¹ * e g) = ((f g)⁻¹ * e g) * e (t ^ n)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using hmul.symm
  have hlabel : ρ (e (t ^ n)) = γ ^ n := by rw [he, map_pow, ht]
  have ha : a = 1 := hfixed n (Nat.ne_of_gt hn) (e (t ^ n)) hlabel a (by
    apply Subtype.ext
    change e (t ^ n) * a.val * (e (t ^ n))⁻¹ = a.val
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one])
  have hval : (f g)⁻¹ * e g = 1 := congrArg Subtype.val ha
  exact (inv_mul_eq_one.mp hval).symm

end ProCGroups
