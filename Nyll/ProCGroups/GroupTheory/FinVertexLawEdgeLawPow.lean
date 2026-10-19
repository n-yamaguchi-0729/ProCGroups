/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.ProCGroups.GroupTheory.FinSubSubModEqFlowSumMulModEqZero
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Choose

/-!
# Fin exists forall vertex Law and edge Law pow of pow add of mod Eq of forall flow sum mul
eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq

namespace TropJac

open Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero.PhiFin
  (IsFlow sum_mul_coboundary_eq_zero)

variable {n m : ℕ}

theorem sum_ite_add (v : Fin m → Fin n) (i : Fin n) (f g : Fin m → ℤ) :
    (∑ x, if v x = i then f x + g x else 0) = (∑ x, if v x = i then f x else 0) + ∑ x, if v x = i
      then g x else 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by
    split_ifs <;> simp only [zero_add]

theorem sum_ite_mul (v : Fin m → Fin n) (i : Fin n) (c : ℤ) (f : Fin m → ℤ) :
    (∑ x, if v x = i then c * f x else 0) = c * ∑ x, if v x = i then f x else 0 := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp only [mul_zero]

/-- The outgoing weight minus the incoming weight at each vertex. -/
def bd (src tgt : Fin m → Fin n) (σ : Fin m → ℤ) : Fin n → ℤ :=
  fun i => (∑ e, if src e = i then σ e else 0) - (∑ e, if tgt e = i then σ e else 0)

/-- The coboundary of a vertex potential, given by its target value minus its source value. -/
def cbd (src tgt : Fin m → Fin n) (β : Fin n → ℤ) : Fin m → ℤ := fun e => β (tgt e) - β (src e)

/-- The linear map combining the edge boundary with weighted edge values plus the potential
coboundary. -/
def Lam (src tgt : Fin m → Fin n) (w : Fin m → ℕ) :
    ((Fin m → ℤ) × (Fin n → ℤ)) →ₗ[ℤ] ((Fin n → ℤ) × (Fin m → ℤ)) where
  toFun p := (bd src tgt p.1, fun e => (w e : ℤ) * p.1 e + cbd src tgt p.2 e)
  map_add' p p' := by
    ext i
    · simp only [bd, Prod.fst_add, Pi.add_apply, Prod.fst_add]
      rw [sum_ite_add src, sum_ite_add tgt]
      ring
    · simp only [cbd, Prod.snd_add, Prod.fst_add, Pi.add_apply]
      ring
  map_smul' c p := by
    ext i
    · simp only [bd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst]
      rw [sum_ite_mul src, sum_ite_mul tgt]
      ring
    · simp only [cbd, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

theorem Lam_apply (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (σ : Fin m → ℤ) (β : Fin n → ℤ) :
    Lam src tgt w (σ, β) = (bd src tgt σ, fun e => (w e : ℤ) * σ e + cbd src tgt β e) := rfl

/-- The pairs whose scalar multiple by the given prime power lies in the range of the incidence
map. -/
def S (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (ℓ : ℕ) (j : ℕ) : Submodule ℤ ((Fin n → ℤ) × (Fin m
  → ℤ)) :=
  (LinearMap.range (Lam src tgt w)).comap ((ℓ : ℤ) ^ j • LinearMap.id)

theorem mem_S (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (ℓ : ℕ) (j : ℕ) (x : (Fin n → ℤ) × (Fin m →
  ℤ)) :
    x ∈ S src tgt w ℓ j ↔ ((ℓ : ℤ) ^ j • x) ∈ LinearMap.range (Lam src tgt w) := Iff.rfl

theorem S_mono (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (ℓ : ℕ) : Monotone (S src tgt w ℓ) := by
  intro j j' hjj' x hx
  rw [mem_S] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjj'
  rw [pow_add, mul_comm, ← smul_smul]
  exact Submodule.smul_mem _ _ hx

theorem exists_S_stable (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (ℓ : ℕ) :
    ∃ N : ℕ, ∀ j, N ≤ j → S src tgt w ℓ N = S src tgt w ℓ j := by
  have h := (monotone_stabilizes_iff_noetherian (R := ℤ) (M := (Fin n → ℤ) × (Fin m → ℤ))).mpr
    inferInstance
    ⟨S src tgt w ℓ, S_mono src tgt w ℓ⟩
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun j hj => hN j hj⟩

private theorem _root_.TropJac.main (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (ℓ : ℕ) (hℓ0 : ℓ ≠ 0)
  :
    ∃ N : ℕ, ∀ (k : ℕ) (d : Fin n → ℤ) (M τ : Fin m → ℤ) (φ : Fin n → ℤ) (σ' : Fin m → ℤ),
      (∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD ((ℓ : ℤ) ^ (k + N))]) →
      (∀ i : Fin n, (ℓ : ℤ) ^ (k + N) * d i + (∑ e, if src e = i then σ' e else 0) +
          (∑ e, if tgt e = i then (ℓ : ℤ) ^ (k + N) * M e - σ' e else 0) = 0) →
      (∀ ε : Fin m → ℤ,
        (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
        (∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * τ e)) =
          ∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * M e - σ' e))) →
      ∃ (σ : Fin m → ℤ) (α : Fin n → ℤ),
        (∀ i : Fin n, (ℓ : ℤ) ^ N * d i + (∑ e, if src e = i then σ e else 0) +
            (∑ e, if tgt e = i then (ℓ : ℤ) ^ N * M e - σ e else 0) = 0) ∧
        (∀ e : Fin m, α (src e) + (ℓ : ℤ) ^ N * τ e =
            α (tgt e) + (ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ N * M e - σ e)) := by
  classical
  obtain ⟨N, hN⟩ := exists_S_stable src tgt w ℓ
  refine ⟨N, ?_⟩
  intro k d M τ φ σ' hτ hV hE
  have hq0' : ((ℓ : ℤ) ^ (k + N)) ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr hℓ0)
  generalize hq : ((ℓ : ℤ) ^ (k + N)) = q at hτ hV hE hq0' ⊢
  have hq0 : q ≠ 0 := hq0'
  have hr' : ∀ e, ∃ r : ℤ, φ (tgt e) - φ (src e) - τ e = q * r := fun e => Int.modEq_iff_dvd.mp (hτ
    e)
  choose r hr using hr'
  set d' : Fin n → ℤ := fun i => d i + ∑ e, if tgt e = i then M e else 0 with hd'
  have hsplit : ∀ (c : ℤ) (s : Fin m → ℤ) (i : Fin n), (∑ e, if tgt e = i then c * M e - s e else
    0) =
      c * (∑ e, if tgt e = i then M e else 0) - ∑ e, if tgt e = i then s e else 0 := by
    intro c s i
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring
  have hbd' : ∀ i, bd src tgt σ' i = -(q * d' i) := by
    intro i
    have h := hV i
    rw [hsplit] at h
    simp only [bd, hd']
    linear_combination h
  have hperp : ∀ ε : Fin m → ℤ, IsFlow src tgt ε →
      (∑ e, ε e * ((w e : ℤ) * σ' e - q * (r e + (w e : ℤ) * M e))) = 0 := by
    intro ε hε
    have h1 := hE ε hε
    have h2 := sum_mul_coboundary_eq_zero src tgt φ ε hε
    have h4 : ∑ e, ε e * (τ e - (w e : ℤ) * (q * M e - σ' e)) = 0 := by
      have : q * ∑ e, ε e * (τ e - (w e : ℤ) * (q * M e - σ' e)) = 0 := by
        rw [Finset.mul_sum, show (∑ e, q * (ε e * (τ e - (w e : ℤ) * (q * M e - σ' e)))) =
          (∑ e, ε e * (q * τ e)) -
            ∑ e, ε e * (q * (w e : ℤ) * (q * M e - σ' e)) from by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun e _ =>
            by ring, h1, sub_self]
      exact (mul_eq_zero.mp this).resolve_left hq0
    have h5 : ∀ e, τ e = (φ (tgt e) - φ (src e)) - q * r e := fun e =>
      by linear_combination (-1 : ℤ) * hr e
    rw [show (∑ e, ε e * ((w e : ℤ) * σ' e - q * (r e + (w e : ℤ) * M e))) =
        (∑ e, ε e * (τ e - (w e : ℤ) * (q * M e - σ' e))) - ∑ e, ε e * (φ (tgt e) - φ (src e)) from
          by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by rw [h5 e]; ring]
    rw [h4, h2, sub_zero]
  obtain ⟨β', hβ'⟩ :=
    Fin.exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero n m src tgt 0
    (fun e => (w e : ℤ) * σ' e - q * (r e + (w e : ℤ) * M e)) (fun ε hε => by
      rw [hperp ε hε])
  have hβ : ∀ e, (w e : ℤ) * σ' e - q * (r e + (w e : ℤ) * M e) = β' (tgt e) - β' (src e) := by
    intro e
    have := hβ' e
    unfold Int.ModEq at this
    rwa [Int.emod_zero, Int.emod_zero] at this
  set x : (Fin n → ℤ) × (Fin m → ℤ) := (fun i => -d' i, fun e => r e + (w e : ℤ) * M e) with hx
  have hxK : x ∈ S src tgt w ℓ (k + N) := by
    rw [mem_S]
    refine ⟨(σ', fun i => -β' i), ?_⟩
    rw [Lam_apply]
    ext i
    · change bd src tgt σ' i = ((ℓ : ℤ) ^ (k + N) • x).1 i
      rw [hbd', Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hx, hq]
      change -(q * d' i) = q * -d' i
      ring
    · change (w i : ℤ) * σ' i + cbd src tgt (fun j => -β' j) i = ((ℓ : ℤ) ^ (k + N) • x).2 i
      rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hx, hq]
      change (w i : ℤ) * σ' i + (-β' (tgt i) - -β' (src i)) = q * (r i + (w i : ℤ) * M i)
      linear_combination hβ i
  have hxN : x ∈ S src tgt w ℓ N := by rw [hN (k + N) (Nat.le_add_left N k)]; exact hxK
  rw [mem_S] at hxN
  obtain ⟨⟨σ, β⟩, hσβ⟩ := hxN
  rw [Lam_apply] at hσβ
  have hσ1 : ∀ i, bd src tgt σ i = (ℓ : ℤ) ^ N * -d' i := fun i => by
    have := congrFun (congrArg Prod.fst hσβ) i
    rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hσ2 : ∀ e, (w e : ℤ) * σ e + (β (tgt e) - β (src e)) = (ℓ : ℤ) ^ N * (r e + (w e : ℤ) * M e)
    := fun e => by
    have := congrFun (congrArg Prod.snd hσβ) e
    rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul] at this
    exact this
  refine ⟨σ, fun i => (ℓ : ℤ) ^ N * φ i - q * β i, ?_, ?_⟩
  · intro i
    rw [hsplit]
    have h1 := hσ1 i
    simp only [bd, hd'] at h1
    linear_combination h1
  · intro e
    dsimp only
    linear_combination (-((ℓ : ℤ) ^ N)) * hr e + q * hσ2 e

end TropJac

theorem
  _root_.Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (_hw : ∀ e, 0 < w e) (ℓ : ℕ) (hℓ : 1 < ℓ) :
    ∃ N : ℕ, ∀ (k : ℕ) (d : Fin n → ℤ) (M τ : Fin m → ℤ) (φ : Fin n → ℤ) (σ' : Fin m → ℤ),
      (∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD ((ℓ : ℤ) ^ (k + N))]) →
      (∀ i : Fin n, (ℓ : ℤ) ^ (k + N) * d i + (∑ e, if src e = i then σ' e else 0) +
          (∑ e, if tgt e = i then (ℓ : ℤ) ^ (k + N) * M e - σ' e else 0) = 0) →
      (∀ ε : Fin m → ℤ,
        (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
        (∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * τ e)) =
          ∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * M e - σ' e))) →
      ∃ (σ : Fin m → ℤ) (α : Fin n → ℤ),
        (∀ i : Fin n, (ℓ : ℤ) ^ N * d i + (∑ e, if src e = i then σ e else 0) +
            (∑ e, if tgt e = i then (ℓ : ℤ) ^ N * M e - σ e else 0) = 0) ∧
        (∀ e : Fin m, α (src e) + (ℓ : ℤ) ^ N * τ e =
            α (tgt e) + (ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ N * M e - σ e)) :=
  TropJac.main src tgt w ℓ (by omega)
end Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
