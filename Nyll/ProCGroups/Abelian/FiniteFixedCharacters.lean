/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

/-!
# A uniform annihilator for invariant finite characters

For an endomorphism of a finite abelian group, the fixed subgroup and the
coinvariant quotient have the same cardinality. Consequently an invariant
character is killed by the cardinality of the fixed subgroup. An embedding of
that subgroup into one common finite group gives a level-independent bound.
-/

namespace ProCGroups.FiniteFixedCharacters

variable {B C : Type*} [AddCommGroup B] [Finite B] [CommMonoid C]

/-- Invariant characters are killed by the order of the actual fixed subgroup. -/
theorem pow_card_fixed_eq_one (F : B →+ B) (χ : AddChar B C)
    (hχ : ∀ b, χ (F b) = χ b) :
    χ ^ Nat.card (F - AddMonoidHom.id B).ker = 1 := by
  let d : B →+ B := F - AddMonoidHom.id B
  have hzero (b : B) : χ (d b) = 1 := by
    change χ (F b - b) = 1
    rw [sub_eq_add_neg]
    rw [χ.map_add_eq_mul, hχ, ← χ.map_add_eq_mul, add_neg_cancel,
      χ.map_zero_eq_one]
  ext b
  change χ b ^ Nat.card d.ker = 1
  rw [← AddSubgroup.index_range (f := d), ← χ.map_nsmul_eq_pow]
  obtain ⟨a, ha⟩ := AddSubgroup.nsmul_index_mem d.range b
  rw [← ha]
  exact hzero a

/-- A common finite target for fixed subgroups supplies a uniform annihilator. -/
theorem pow_card_target_eq_one {S : Type*} [AddCommGroup S] [Finite S]
    (F : B →+ B) (j : (F - AddMonoidHom.id B).ker →+ S)
    (hj : Function.Injective j) (χ : AddChar B C)
    (hχ : ∀ b, χ (F b) = χ b) : χ ^ Nat.card S = 1 := by
  obtain ⟨a, ha⟩ := AddSubgroup.card_dvd_of_injective j hj
  rw [ha, pow_mul, pow_card_fixed_eq_one F χ hχ, one_pow]

/-- An injective left pairing transfers the invariant-character bound to its
first argument. No perfect duality or semisimplicity assumption is required. -/
theorem nsmul_eq_zero_of_invariant_pairing {S : Type*} [AddCommGroup S] [Finite S]
    (F : B →+ B) (j : (F - AddMonoidHom.id B).ker →+ S)
    (hj : Function.Injective j) (P : B →+ Additive (AddChar B C))
    (hP : Function.Injective P) (v : B)
    (hv : ∀ b, Additive.toMul (P v) (F b) = Additive.toMul (P v) b) :
    Nat.card S • v = 0 := by
  apply hP
  rw [map_nsmul, map_zero]
  change (Additive.toMul (P v)) ^ Nat.card S = 1
  exact pow_card_target_eq_one F j hj (Additive.toMul (P v)) hv

end ProCGroups.FiniteFixedCharacters
