/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.RestrictedTateModule
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Torsion-freeness for every restricted Tate module

No saturation condition on the multiplicative index set is needed. For prime
torsion, a coordinate is killed using its square index if the prime divides
its index, and coprimality otherwise. Prime induction handles every annihilator.
-/

namespace ProCGroups.RestrictedTateModule

variable {M : Type*} [AddCommGroup M] {S : Submonoid ℕ+}

/-- A restricted compatible torsion family has no nonzero prime torsion. -/
theorem eq_zero_of_prime_nsmul_eq_zero (x : RestrictedTateModule M S)
    {p : ℕ} (hp : p.Prime) (hx : p • x = 0) : x = 0 := by
  have hval (n : S) : p • evaluation M S n x = 0 := by
    have h := congrArg (evaluation M S n) hx
    rw [map_nsmul, map_zero] at h
    exact h
  apply ext
  intro n
  rw [map_zero]
  by_cases hdiv : p ∣ (n.1 : ℕ)
  · obtain ⟨a, ha⟩ := hdiv
    calc
      evaluation M S n x = (n.1 : ℕ) • evaluation M S (n * n) x :=
        (evaluation_compatible x n n).symm
      _ = 0 := by rw [ha, Nat.mul_comm p a, mul_smul, hval, nsmul_zero]
  · have hn : (n.1 : ℕ) • evaluation M S n x = 0 := (projection M S n x).property
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hp.coprime_iff_not_dvd.mpr hdiv)
      (addOrderOf_dvd_of_nsmul_eq_zero (hval n))
      (addOrderOf_dvd_of_nsmul_eq_zero hn)

/-- No nonzero positive-integer torsion occurs, even if the annihilator is
not among the allowed indices. -/
theorem eq_zero_of_nsmul_eq_zero (x : RestrictedTateModule M S) {n : ℕ}
    (hn : 0 < n) (hx : n • x = 0) : x = 0 := by
  have hall : ∀ n : ℕ, ∀ y : RestrictedTateModule M S, 0 < n → n • y = 0 → y = 0 := by
    apply induction_on_primes
    · intro y h
      exact False.elim (Nat.not_lt_zero 0 h)
    · intro y _ hy
      simpa only [one_nsmul] using hy
    · intro p a hp ih y hpa hy
      have ha : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hpa)
      apply ih y ha
      apply eq_zero_of_prime_nsmul_eq_zero (a • y) hp
      rwa [← mul_smul]
  exact hall n x hn hx

instance : IsAddTorsionFree (RestrictedTateModule M S) where
  nsmul_right_injective := by
    intro n hn x y hxy
    change n • x = n • y at hxy
    apply sub_eq_zero.mp
    apply eq_zero_of_nsmul_eq_zero (x - y) (Nat.pos_of_ne_zero hn)
    rw [nsmul_sub, hxy, sub_self]

end ProCGroups.RestrictedTateModule
