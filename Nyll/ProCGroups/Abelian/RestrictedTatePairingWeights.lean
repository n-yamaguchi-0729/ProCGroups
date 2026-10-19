/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FiniteFixedCharacters
import Nyll.ProCGroups.Abelian.RestrictedTateTorsionFree

/-!
# Scalar eigenvectors detected by finite-level pairings

An injective left pairing turns a scalar eigenvector into an invariant
character. A common finite group containing all fixed torsion subgroups then
annihilates the whole compatible family, which is torsion-free. Pairings need
not be compatible across levels, and the common cardinal need not be an
allowed index.
-/

namespace ProCGroups.FiniteFixedCharacters

/-- Coprime powers can be cancelled among elements killed by a common power,
even in a monoid with zero. -/
theorem pow_cancel_of_coprime {C : Type*} [Monoid C] {u v : C} {q n : ℕ}
    (hqn : Nat.Coprime q n) (hu : u ^ n = 1) (hv : v ^ n = 1)
    (h : u ^ q = v ^ q) : u = v := by
  have huv : (u, v) ^ n = (1 : C × C) := Prod.ext hu hv
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (hqn.of_dvd_right (orderOf_dvd_of_pow_eq_one huv))
  have hmu : (u ^ q) ^ m = u := congrArg Prod.fst hm
  have hmv : (v ^ q) ^ m = v := congrArg Prod.snd hm
  exact hmu.symm.trans ((congrArg (fun x : C => x ^ m) h).trans hmv)

/-- The multiplier eigenspace gives invariant characters under a pairing
whose multiplier is coprime to the torsion exponent. -/
theorem pairing_invariant_of_scalar {B C : Type*} [AddCommGroup B] [CommMonoid C]
    (F : B →+ B) (P : B →+ Additive (AddChar B C)) {q n : ℕ}
    (hqn : Nat.Coprime q n) (hn : ∀ b : B, n • b = 0)
    (hcompat : ∀ a b, Additive.toMul (P (F a)) (F b) =
      (Additive.toMul (P a) b) ^ q)
    (v : B) (hv : F v = q • v) :
    ∀ b, Additive.toMul (P v) (F b) = Additive.toMul (P v) b := by
  let e (a b : B) := Additive.toMul (P a) b
  have hroot (a b : B) : e a b ^ n = 1 := by
    change (Additive.toMul (P a)) b ^ n = 1
    rw [← AddChar.map_nsmul_eq_pow, hn b, AddChar.map_zero_eq_one]
  have hleft (k : ℕ) (a b : B) : e (k • a) b = e a b ^ k := by
    change Additive.toMul (P (k • a)) b = _
    rw [map_nsmul]
    rfl
  intro b
  apply pow_cancel_of_coprime hqn (hroot v (F b)) (hroot v b)
  have h := hcompat v b
  change e (F v) (F b) = e v b ^ q at h
  rw [hv, hleft] at h
  exact h

end ProCGroups.FiniteFixedCharacters

namespace ProCGroups.RestrictedTateModule

/-- Uniform finite fixed-subgroup bounds and nondegenerate finite-level
pairings kill scalar eigenvectors in every restricted Tate module. -/
theorem eq_zero_of_scalar_pairing
    {M C S : Type*} [AddCommGroup M] [CommMonoid C] [AddCommGroup S] [Finite S]
    {I : Submonoid ℕ+} [∀ n : I, Finite (torsionLevel M n.1)]
    (F : ∀ n : I, torsionLevel M n.1 →+ torsionLevel M n.1)
    (j : ∀ n : I, (F n - AddMonoidHom.id (torsionLevel M n.1)).ker →+ S)
    (hj : ∀ n, Function.Injective (j n))
    (P : ∀ n : I, torsionLevel M n.1 →+
      Additive (AddChar (torsionLevel M n.1) C))
    (hP : ∀ n, Function.Injective (P n))
    (q : ℕ) (hq : ∀ n : I, Nat.Coprime q (n.1 : ℕ))
    (hcompat : ∀ n a b, Additive.toMul (P n (F n a)) (F n b) =
      (Additive.toMul (P n a) b) ^ q)
    (x : RestrictedTateModule M I)
    (hx : ∀ n, F n (projection M I n x) = q • projection M I n x) : x = 0 := by
  apply eq_zero_of_nsmul_eq_zero x (Nat.card_pos (α := S))
  apply ext
  intro n
  rw [map_nsmul, map_zero]
  have hn (b : torsionLevel M n.1) : (n.1 : ℕ) • b = 0 := by
    apply Subtype.ext
    exact b.property
  have h := FiniteFixedCharacters.nsmul_eq_zero_of_invariant_pairing
    (F n) (j n) (hj n) (P n) (hP n) (projection M I n x)
    (FiniteFixedCharacters.pairing_invariant_of_scalar
      (F n) (P n) (hq n) hn (hcompat n) (projection M I n x) (hx n))
  exact congrArg (fun b : torsionLevel M n.1 => (b : M)) h

end ProCGroups.RestrictedTateModule
