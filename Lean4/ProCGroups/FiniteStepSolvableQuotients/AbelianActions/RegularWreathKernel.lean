/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.WreathProducts
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.FaithfulKernel
import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Nontrivial.Defs

set_option autoImplicit false

/-!
# Faithful elementary abelian kernels from regular wreath products

The right projection of the regular wreath product has a commutative kernel
when the coefficient group is commutative. A nontrivial coefficient group
makes the quotient's conjugation action faithful, by evaluation on a function
supported at the identity. Finite coefficients killed by `q` give an actual
elementary abelian kernel. No restriction is placed on the finite quotient
group's order.
-/

namespace ProCGroups

universe u

namespace FiniteGroupClass

/-- An elementary abelian group of prime exponent belongs to every finite
Sigma class containing that prime. -/
theorem sigmaGroup_of_abelianExponent {sigma : Set ℕ} (q : ℕ) [Fact q.Prime]
    {A : Type u} [Group A] (hq : q ∈ sigma) (hA : abelianExponent q A) :
    sigmaGroup sigma A := by
  have : Finite A := hA.1
  have hp : IsPGroup q A := isPGroup_iff_pow_pow_eq_one.mpr (by
    intro a
    exact ⟨1, by simpa only [pow_one] using hA.2.2 a⟩)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  refine ⟨inferInstance, ?_⟩
  rw [hn]
  exact IsSigmaNumber.prime_pow_of_mem hq (Fact.out : q.Prime)

end FiniteGroupClass

namespace FiniteStepSolvableQuotients

open WreathProducts

variable {A B : Type u} [CommGroup A] [Group B]

/-- The kernel of the actual right projection of a regular wreath product
is commutative. -/
theorem regularWreathKernel_commute
    (a b : (SemidirectProduct.rightHom : PermutationalWreathProduct A B B →* B).ker) :
    Commute (a : PermutationalWreathProduct A B B)
      (b : PermutationalWreathProduct A B B) := by
  have ha : (a : PermutationalWreathProduct A B B).right = 1 := a.property
  have hb : (b : PermutationalWreathProduct A B B).right = 1 := b.property
  change (a : PermutationalWreathProduct A B B) * b =
    (b : PermutationalWreathProduct A B B) * a
  apply SemidirectProduct.ext
  · simpa only [SemidirectProduct.mul_left, ha, hb, map_one, MulAut.one_apply] using
      mul_comm (a : PermutationalWreathProduct A B B).left
        (b : PermutationalWreathProduct A B B).left
  · change (a : PermutationalWreathProduct A B B).right *
        (b : PermutationalWreathProduct A B B).right =
      (b : PermutationalWreathProduct A B B).right *
        (a : PermutationalWreathProduct A B B).right
    rw [ha, hb]

/-- A nontrivial coefficient group makes the actual regular wreath kernel
conjugation action faithful. -/
theorem regularWreathKernel_conjugation_injective [Nontrivial A] :
    Function.Injective (abelianKernelConjugation
      (SemidirectProduct.rightHom : PermutationalWreathProduct A B B →* B)
      SemidirectProduct.rightHom_surjective
      (regularWreathKernel_commute (A := A) (B := B))) := by
  classical
  apply (abelianKernelConjugation_injective_iff
    (SemidirectProduct.rightHom : PermutationalWreathProduct A B B →* B)
    SemidirectProduct.rightHom_surjective
    (regularWreathKernel_commute (A := A) (B := B))).mpr
  intro e he
  change e.right = 1
  by_contra hright
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  let f : B → A := fun b => if b = 1 then a else 1
  let n : (SemidirectProduct.rightHom : PermutationalWreathProduct A B B →* B).ker :=
    ⟨SemidirectProduct.inl f, SemidirectProduct.rightHom_inl f⟩
  have hz := congrArg (fun z : PermutationalWreathProduct A B B => z.left 1) (he n).eq
  change e.left 1 * f (e.right⁻¹ * 1) = f 1 * e.left ((1 : B)⁻¹ * 1) at hz
  have hinv : e.right⁻¹ ≠ 1 := inv_ne_one.mpr hright
  simp only [mul_one, inv_one, f, ite_eq_right hinv, ite_eq_left rfl] at hz
  have haone : a = 1 := (mul_right_cancel ((one_mul (e.left 1)).trans hz)).symm
  exact ha haone

/-- Finite coefficients killed by `q` produce an actual finite abelian
kernel of exponent dividing `q`. -/
theorem regularWreathKernel_mem_abelianExponent [Finite A] [Finite B]
    (q : ℕ) (hpow : ∀ a : A, a ^ q = 1) :
    FiniteGroupClass.abelianExponent q
      (SemidirectProduct.rightHom : PermutationalWreathProduct A B B →* B).ker := by
  let K : Subgroup (PermutationalWreathProduct A B B) := SemidirectProduct.rightHom.ker
  have hleft : Function.Injective (fun x : K => (x : PermutationalWreathProduct A B B).left) := by
    intro x y hxy
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact hxy
    · exact x.property.trans y.property.symm
  have : Finite K := Finite.of_injective
    (fun x : K => (x : PermutationalWreathProduct A B B).left) hleft
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x y
    exact Subtype.ext (regularWreathKernel_commute (A := A) (B := B) x y).eq
  · intro x
    have hx : (SemidirectProduct.inl (x : PermutationalWreathProduct A B B).left :
        PermutationalWreathProduct A B B) = x := by
      apply SemidirectProduct.ext
      · rfl
      · exact x.property.symm
    have hp : (x : PermutationalWreathProduct A B B).left ^ q = 1 := by
      funext b
      exact hpow ((x : PermutationalWreathProduct A B B).left b)
    apply Subtype.ext
    change (x : PermutationalWreathProduct A B B) ^ q = 1
    rw [← hx, ← map_pow, hp, map_one]

omit [CommGroup A] in
/-- The concrete cyclic coefficient group obtained from `ZMod q` gives an
elementary abelian kernel for every finite quotient group. -/
theorem regularWreathKernel_cyclicZMod_mem_abelianExponent [Finite B]
    (q : ℕ) [Fact q.Prime] :
    FiniteGroupClass.abelianExponent q
      (SemidirectProduct.rightHom :
        PermutationalWreathProduct (ULift.{u} (Multiplicative (ZMod q))) B B →* B).ker := by
  apply regularWreathKernel_mem_abelianExponent q
  intro a
  apply (MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod q)) ≃*
    Multiplicative (ZMod q)).injective
  change q • Multiplicative.toAdd a.down = (0 : ZMod q)
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end FiniteStepSolvableQuotients

end ProCGroups
