/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Functorial maps of the existing full Tate module

An additive homomorphism acts on the actual torsion coordinates. No new
inverse-limit object or topology is introduced.
-/

namespace ProCGroups.FullTateModule

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- Apply an additive homomorphism to every actual torsion coordinate. -/
def map (f : M →+ N) : FullTateModule M →+ FullTateModule N where
  toFun x := ⟨fun n => ⟨f (evaluation M n x), by
    change (n : ℕ) • f (evaluation M n x) = 0
    rw [← map_nsmul, evaluation_annihilated, map_zero]⟩, by
      intro n m
      apply Subtype.ext
      change (m : ℕ) • f (evaluation M (n * m) x) = f (evaluation M n x)
      rw [← map_nsmul, evaluation_compatible]⟩
  map_zero' := by
    apply ext
    intro n
    change f (evaluation M n 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    apply ext
    intro n
    change f (evaluation M n (x + y)) =
      f (evaluation M n x) + f (evaluation M n y)
    rw [map_add, map_add]

@[simp] theorem evaluation_map (f : M →+ N) (x : FullTateModule M) (n : ℕ+) :
    evaluation N n (map f x) = f (evaluation M n x) := rfl

@[simp] theorem map_id (x : FullTateModule M) : map (AddMonoidHom.id M) x = x := by
  apply ext
  intro n
  rfl

@[simp] theorem map_comp (f : M →+ N) (g : N →+ P) (x : FullTateModule M) :
    map (g.comp f) x = map g (map f x) := by
  apply ext
  intro n
  rfl

/-- Coordinatewise transport is continuous for the existing inverse-limit topology. -/
theorem continuous_map (f : M →+ N) : Continuous (map f) := by
  let (n : ℕ+) := torsionLevelTopology M n
  let (n : ℕ+) := torsionLevelTopology N n
  have (n : ℕ+) : DiscreteTopology (torsionLevel M n) := ⟨rfl⟩
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  let fn : torsionLevel M n → torsionLevel N n := fun x =>
    ⟨f x.val, by
      change (n : ℕ) • f x.val = 0
      rw [← map_nsmul, x.property, map_zero]⟩
  exact (continuous_of_discreteTopology : Continuous fn).comp (continuous_projection M n)

/-- The coordinatewise map in the multiplicative notation of fundamental groups. -/
def mapHom (f : M →+ N) : Multiplicative (FullTateModule M) →ₜ*
    Multiplicative (FullTateModule N) where
  toFun x := Multiplicative.ofAdd (map f (Multiplicative.toAdd x))
  map_one' := (map f).map_zero
  map_mul' x y := (map f).map_add x y
  continuous_toFun := continuous_map f

/-- An equivalence of the actual point groups transports the existing full Tate module. -/
noncomputable def mapEquiv (e : M ≃+ N) : Multiplicative (FullTateModule M) ≃ₜ*
    Multiplicative (FullTateModule N) :=
  ProCGroups.ContinuousMulEquiv.ofHomInv (mapHom e.toAddMonoidHom)
    (mapHom e.symm.toAddMonoidHom)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change e.symm (e (evaluation M n (Multiplicative.toAdd x))) =
        evaluation M n (Multiplicative.toAdd x)
      exact e.symm_apply_apply _)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change e (e.symm (evaluation N n (Multiplicative.toAdd x))) =
        evaluation N n (Multiplicative.toAdd x)
      exact e.apply_symm_apply _)

@[simp] theorem mapEquiv_apply (e : M ≃+ N) (x : Multiplicative (FullTateModule M)) :
    mapEquiv e x = Multiplicative.ofAdd (map e.toAddMonoidHom (Multiplicative.toAdd x)) := rfl

end ProCGroups.FullTateModule
