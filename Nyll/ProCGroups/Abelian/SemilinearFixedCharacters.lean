/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.FiniteFixedCharacters

/-!
# Semilinear characters under a finite-level perfect pairing

A character transforming by the coefficient automorphism is represented
by a fixed point of the original paired group. If those fixed points embed
in one finite subgroup, its order annihilates the character. The same bound
can therefore be used at every torsion level, without assuming compatible
choices of pairings or semisimplicity.
-/

@[expose] public section

namespace ProCGroups.FiniteFixedCharacters

variable {B M C : Type*} [AddCommGroup B] [AddCommGroup M] [CommMonoid C]

/-- The vector representing a semilinear character is fixed, with the
coefficient automorphism retained on both sides of the original pairing. -/
theorem representing_vector_fixed_of_semilinear_character
    (F : B ≃+ B) (σ : C →* C)
    (P : B ≃+ Additive (AddChar B C))
    (hP : ∀ a b, Additive.toMul (P (F a)) (F b) =
      σ (Additive.toMul (P a) b))
    (χ : AddChar B C) (hχ : ∀ b, χ (F b) = σ (χ b)) :
    F (P.symm (Additive.ofMul χ)) = P.symm (Additive.ofMul χ) := by
  let v := P.symm (Additive.ofMul χ)
  have hv (b : B) : Additive.toMul (P v) b = χ b :=
    congrArg (fun ψ : Additive (AddChar B C) => ψ.toMul b)
      (P.apply_symm_apply (Additive.ofMul χ))
  apply P.injective
  apply Additive.toMul.injective
  ext b
  obtain ⟨c, rfl⟩ := F.surjective b
  exact (hP v c).trans ((congrArg σ (hv c)).trans
    ((hχ c).symm.trans (hv (F c)).symm))

/-- One finite subgroup containing the represented fixed points gives a
uniform annihilator for all semilinear characters. -/
theorem pow_card_target_eq_one_of_semilinear_pairing
    (F : B ≃+ B) (σ : C →* C)
    (P : B ≃+ Additive (AddChar B C))
    (hP : ∀ a b, Additive.toMul (P (F a)) (F b) =
      σ (Additive.toMul (P a) b))
    (j : B →+ M) (hj : Function.Injective j)
    (S : AddSubgroup M) [Finite S]
    (hS : ∀ b, F b = b → j b ∈ S)
    (χ : AddChar B C) (hχ : ∀ b, χ (F b) = σ (χ b)) :
    χ ^ Nat.card S = 1 := by
  let v := P.symm (Additive.ofMul χ)
  have hv : F v = v :=
    representing_vector_fixed_of_semilinear_character F σ P hP χ hχ
  have hzero : Nat.card S • v = 0 := by
    apply hj
    rw [map_nsmul, map_zero]
    exact congrArg (fun a : S => (a : M))
      (card_nsmul_eq_zero' (x := (⟨j v, hS v hv⟩ : S)))
  have h := congrArg P hzero
  rw [map_nsmul, map_zero] at h
  change Nat.card S • P (P.symm (Additive.ofMul χ)) = 0 at h
  rw [P.apply_symm_apply] at h
  exact congrArg Additive.toMul h

end ProCGroups.FiniteFixedCharacters
