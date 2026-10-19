/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.RestrictedTateModule
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Transport of restricted Tate modules through their actual torsion levels

Compatible additive maps on the existing discrete levels act continuously on
the existing compatible-family subtype. Levelwise equivalences give a
continuous equivalence without an equivalence of the full point groups.
-/

namespace ProCGroups.RestrictedTateModule

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {S : Submonoid ℕ+}

/-- A compatible family of additive maps on torsion levels acts on the restricted module. -/
def mapLevels (f : ∀ n : S, torsionLevel M n.1 →+ torsionLevel N n.1)
    (hf : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (f (n * m) x) = f n (torsionTransition M n.1 m.1 x)) :
    RestrictedTateModule M S →+ RestrictedTateModule N S where
  toFun x := ⟨fun n => f n (projection M S n x), by
    intro n m
    rw [hf]
    exact congrArg (f n) (x.2 n m)⟩
  map_zero' := by
    apply ext
    intro n
    exact congrArg Subtype.val ((f n).map_zero)
  map_add' x y := by
    apply ext
    intro n
    exact congrArg Subtype.val ((f n).map_add (projection M S n x) (projection M S n y))

@[simp] theorem projection_mapLevels
    (f : ∀ n : S, torsionLevel M n.1 →+ torsionLevel N n.1)
    (hf : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (f (n * m) x) = f n (torsionTransition M n.1 m.1 x))
    (x : RestrictedTateModule M S) (n : S) :
    projection N S n (mapLevels f hf x) = f n (projection M S n x) := rfl

/-- Continuity uses the original product topology of discrete torsion levels. -/
theorem continuous_mapLevels
    (f : ∀ n : S, torsionLevel M n.1 →+ torsionLevel N n.1)
    (hf : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (f (n * m) x) = f n (torsionTransition M n.1 m.1 x)) :
    Continuous (mapLevels f hf) := by
  let (n : ℕ+) := FullTateModule.torsionLevelTopology M n
  let (n : ℕ+) := FullTateModule.torsionLevelTopology N n
  have (n : ℕ+) : DiscreteTopology (torsionLevel M n) := ⟨rfl⟩
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology : Continuous (f n)).comp (continuous_projection M S n)

/-- The same map in the multiplicative notation of fundamental groups. -/
def mapLevelsHom
    (f : ∀ n : S, torsionLevel M n.1 →+ torsionLevel N n.1)
    (hf : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (f (n * m) x) = f n (torsionTransition M n.1 m.1 x)) :
    Multiplicative (RestrictedTateModule M S) →ₜ*
      Multiplicative (RestrictedTateModule N S) where
  toFun x := Multiplicative.ofAdd (mapLevels f hf (Multiplicative.toAdd x))
  map_one' := (mapLevels f hf).map_zero
  map_mul' x y := (mapLevels f hf).map_add x y
  continuous_toFun := continuous_mapLevels f hf

/-- Compatible equivalences of actual torsion levels transport the restricted Tate module. -/
noncomputable def equivLevels
    (e : ∀ n : S, torsionLevel M n.1 ≃+ torsionLevel N n.1)
    (he : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (e (n * m) x) = e n (torsionTransition M n.1 m.1 x)) :
    Multiplicative (RestrictedTateModule M S) ≃ₜ*
      Multiplicative (RestrictedTateModule N S) := by
  have hi : ∀ (n m : S) (y : torsionLevel N (n * m).1),
      torsionTransition M n.1 m.1 ((e (n * m)).symm y) =
        (e n).symm (torsionTransition N n.1 m.1 y) := by
    intro n m y
    apply (e n).injective
    rw [← he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact ProCGroups.ContinuousMulEquiv.ofHomInv
    (mapLevelsHom (fun n => (e n).toAddMonoidHom) he)
    (mapLevelsHom (fun n => (e n).symm.toAddMonoidHom) hi)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change (((e n).symm (e n (projection M S n (Multiplicative.toAdd x)))) : M) = _
      rw [AddEquiv.symm_apply_apply]
      rfl)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change ((e n ((e n).symm (projection N S n (Multiplicative.toAdd x)))) : N) = _
      rw [AddEquiv.apply_symm_apply]
      rfl)

/-- Transport retains the specified equivalence at every actual torsion coordinate. -/
@[simp] theorem projection_equivLevels
    (e : ∀ n : S, torsionLevel M n.1 ≃+ torsionLevel N n.1)
    (he : ∀ (n m : S) (x : torsionLevel M (n * m).1),
      torsionTransition N n.1 m.1 (e (n * m) x) = e n (torsionTransition M n.1 m.1 x))
    (x : Multiplicative (RestrictedTateModule M S)) (n : S) :
    projection N S n (Multiplicative.toAdd (equivLevels e he x)) =
      e n (projection M S n (Multiplicative.toAdd x)) := rfl

end ProCGroups.RestrictedTateModule
