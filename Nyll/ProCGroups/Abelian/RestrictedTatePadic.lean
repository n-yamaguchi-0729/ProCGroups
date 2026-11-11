/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The p-adic action on actual restricted torsion families

Each actual n-torsion group has its canonical ZMod n action. For prime-power
indices, the residue of a p-adic integer acts at that same torsion coordinate.
Compatibility of the residue maps preserves the original multiplication
transitions, giving the existing restricted Tate module a p-adic module structure.
-/

@[expose] public section

noncomputable section

universe u v

namespace ProCGroups

variable (M : Type u) [AddCommGroup M]

/-- The canonical scalar action on the actual subgroup killed by n. -/
instance torsionLevelZModModule (n : ℕ+) : Module (ZMod (n : ℕ)) (torsionLevel M n) :=
  AddCommGroup.zmodModule fun x => Subtype.ext x.property

namespace RestrictedTateModule

variable (p : ℕ+)

/-- The logarithm of a power index recovers its original positive integer. -/
theorem primePowerIndex_pow_log (n : Submonoid.powers p) :
    (p : ℕ) ^ Submonoid.log n = (n.1 : ℕ) := by
  exact congrArg (fun q : Submonoid.powers p => (q.1 : ℕ))
    (Submonoid.pow_log_eq_self n)

variable [Fact (p : ℕ).Prime]

/-- Positive powers of a prime have unique exponents. -/
theorem primePower_pow_injective : Function.Injective (fun n : ℕ => p ^ n) := by
  intro i j h
  exact Nat.pow_right_injective (Fact.out : (p : ℕ).Prime).two_le
    (congrArg (fun q : ℕ+ => (q : ℕ)) h)

/-- Reduction to the modulus of the original restricted torsion coordinate. -/
def primePowerResidue (n : Submonoid.powers p) : ℤ_[(p : ℕ)] →+* ZMod (n.1 : ℕ) :=
  (ZMod.ringEquivCongr (primePowerIndex_pow_log p n)).toRingHom.comp
    (PadicInt.toZModPow (Submonoid.log n))

/-- The residue acts through the usual finite p-adic approximation. -/
theorem primePowerResidue_appr (n : Submonoid.powers p) (a : ℤ_[(p : ℕ)]) :
    primePowerResidue p n a = (a.appr (Submonoid.log n) : ZMod (n.1 : ℕ)) := by
  change ZMod.ringEquivCongr (primePowerIndex_pow_log p n)
    (a.appr (Submonoid.log n) : ZMod ((p : ℕ) ^ Submonoid.log n)) = _
  exact map_natCast _ _

/-- At the original p-power index the residue is exactly PadicInt.toZModPow. -/
theorem primePowerResidue_pow (n : ℕ) (a : ℤ_[(p : ℕ)]) :
    primePowerResidue p (Submonoid.pow p n) a = PadicInt.toZModPow n a := by
  change primePowerResidue p (Submonoid.pow p n) a = (a.appr n : ZMod ((p : ℕ) ^ n))
  rw [primePowerResidue_appr, Submonoid.log_pow_eq_self (primePower_pow_injective p)]
  rfl

/-- Restrict scalars along the actual p-adic residue at a torsion coordinate. -/
abbrev torsionLevelPadicModule (n : Submonoid.powers p) :
    Module ℤ_[(p : ℕ)] (torsionLevel M n.1) :=
  Module.compHom (torsionLevel M n.1) (primePowerResidue p n)

attribute [local instance] torsionLevelPadicModule

/-- The p-adic scalar action preserves the original point and its integer multiplication. -/
theorem torsionLevel_padic_smul_coe (n : Submonoid.powers p) (a : ℤ_[(p : ℕ)])
    (x : torsionLevel M n.1) :
    ((a • x : torsionLevel M n.1) : M) = a.appr (Submonoid.log n) • (x : M) := by
  change ((primePowerResidue p n a • x : torsionLevel M n.1) : M) = _
  rw [primePowerResidue_appr, Nat.cast_smul_eq_nsmul]
  exact map_nsmul (torsionLevel M n.1).subtype (a.appr (Submonoid.log n)) x

/-- Approximations at a multiple index have the same residue at the smaller index. -/
theorem primePower_appr_cast_compatible (a : ℤ_[(p : ℕ)]) (n m : Submonoid.powers p) :
    (a.appr (Submonoid.log (n * m)) : ZMod (n.1 : ℕ)) =
      (a.appr (Submonoid.log n) : ZMod (n.1 : ℕ)) := by
  have hle : Submonoid.log n ≤ Submonoid.log (n * m) := by
    rw [Submonoid.log_mul (primePower_pow_injective p)]
    exact Nat.le_add_right _ _
  have h := congrArg
    (fun f : ℤ_[(p : ℕ)] →+* ZMod ((p : ℕ) ^ Submonoid.log n) => f a)
    (PadicInt.zmod_cast_comp_toZModPow (Submonoid.log n) (Submonoid.log (n * m)) hle)
  change ZMod.castHom (pow_dvd_pow (p : ℕ) hle) (ZMod ((p : ℕ) ^ Submonoid.log n))
      (a.appr (Submonoid.log (n * m)) : ZMod ((p : ℕ) ^ Submonoid.log (n * m))) =
    (a.appr (Submonoid.log n) : ZMod ((p : ℕ) ^ Submonoid.log n)) at h
  rw [ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow (p : ℕ) hle)] at h
  have ht := congrArg (ZMod.ringEquivCongr (primePowerIndex_pow_log p n)) h
  simpa only [map_natCast] using ht

/-- Original multiplication transitions commute with the coordinate p-adic actions. -/
theorem torsionTransition_padic_smul (n m : Submonoid.powers p) (a : ℤ_[(p : ℕ)])
    (x : torsionLevel M (n * m).1) :
    torsionTransition M n.1 m.1 (a • x) = a • torsionTransition M n.1 m.1 x := by
  apply Subtype.ext
  change (m.1 : ℕ) • ((a • x : torsionLevel M (n * m).1) : M) = _
  rw [torsionLevel_padic_smul_coe, torsionLevel_padic_smul_coe]
  change (m.1 : ℕ) • (a.appr (Submonoid.log (n * m)) • (x : M)) =
    a.appr (Submonoid.log n) • ((m.1 : ℕ) • (x : M))
  rw [smul_comm (m.1 : ℕ) (a.appr (Submonoid.log (n * m))) (x : M)]
  have h := congrArg
    (fun c : ZMod (n.1 : ℕ) => c • torsionTransition M n.1 m.1 x)
    (primePower_appr_cast_compatible p a n m)
  have hn : a.appr (Submonoid.log (n * m)) • torsionTransition M n.1 m.1 x =
      a.appr (Submonoid.log n) • torsionTransition M n.1 m.1 x := by
    simpa only [Nat.cast_smul_eq_nsmul] using h
  exact congrArg (fun y : torsionLevel M n.1 => (y : M)) hn

/-- The original additive subgroup of compatible families is closed under p-adic scalars. -/
def primePowerCompatibleSubmodule :
    Submodule ℤ_[(p : ℕ)] (∀ n : Submonoid.powers p, torsionLevel M n.1) where
  toAddSubmonoid := (restrictedCompatibleTorsionFamilies M (Submonoid.powers p)).toAddSubmonoid
  smul_mem' := by
    intro a x hx n m
    change torsionTransition M n.1 m.1 (a • x (n * m)) = a • x n
    rw [torsionTransition_padic_smul, hx n m]

/-- The p-adic action on the existing restricted Tate module, with its original additive group. -/
instance instPrimePowerModule :
    Module ℤ_[(p : ℕ)] (RestrictedTateModule M (Submonoid.powers p)) :=
  inferInstanceAs (Module ℤ_[(p : ℕ)] ↥(primePowerCompatibleSubmodule M p))

/-- Projection uses the actual residue action on the original finite torsion group. -/
theorem projection_padic_smul (n : Submonoid.powers p) (a : ℤ_[(p : ℕ)])
    (x : RestrictedTateModule M (Submonoid.powers p)) :
    projection M _ n (a • x) = primePowerResidue p n a • projection M _ n x := rfl

/-- At every p-power coordinate the scalar is the canonical p-adic reduction. -/
theorem projection_padic_smul_pow (n : ℕ) (a : ℤ_[(p : ℕ)])
    (x : RestrictedTateModule M (Submonoid.powers p)) :
    projection M _ (Submonoid.pow p n) (a • x) =
      (show ZMod (((Submonoid.pow p n).1 : ℕ)) from
        PadicInt.toZModPow (p := (p : ℕ)) n a) •
        projection M _ (Submonoid.pow p n) x := by
  rw [projection_padic_smul, primePowerResidue_pow]

/-- Evaluation of a p-adic multiple is integer multiplication at the same actual torsion point. -/
theorem evaluation_padic_smul (n : Submonoid.powers p) (a : ℤ_[(p : ℕ)])
    (x : RestrictedTateModule M (Submonoid.powers p)) :
    evaluation M _ n (a • x) = a.appr (Submonoid.log n) • evaluation M _ n x := by
  exact torsionLevel_padic_smul_coe M p n a (projection M _ n x)

variable {M} {N : Type v} [AddCommGroup N]

/-- The existing map of compatible torsion families is p-adic linear. -/
noncomputable def mapLinear (f : M →+ N) :
    RestrictedTateModule M (Submonoid.powers p) →ₗ[ℤ_[(p : ℕ)]]
      RestrictedTateModule N (Submonoid.powers p) where
  toFun := map (S := Submonoid.powers p) f
  map_add' := (map (S := Submonoid.powers p) f).map_add
  map_smul' := by
    intro a x
    change map (S := Submonoid.powers p) f (a • x) =
      a • map (S := Submonoid.powers p) f x
    apply ext
    intro n
    rw [evaluation_map, evaluation_padic_smul, evaluation_padic_smul, evaluation_map]
    exact map_nsmul f _ _

/-- The linear map has exactly the original pointwise evaluation. -/
@[simp] theorem evaluation_mapLinear (f : M →+ N)
    (x : RestrictedTateModule M (Submonoid.powers p)) (n : Submonoid.powers p) :
    evaluation N _ n (mapLinear p f x) = f (evaluation M _ n x) := rfl

end RestrictedTateModule

end ProCGroups
