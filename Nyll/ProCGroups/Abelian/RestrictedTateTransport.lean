/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Transport of restricted Tate modules through their actual torsion levels

Compatible additive maps on the existing discrete levels act continuously on
the existing compatible-family subtype. Levelwise equivalences give a
continuous equivalence without an equivalence of the full point groups.
-/

@[expose] public section

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

/-- Restrict an additive map to the actual torsion subgroup at a positive index. -/
def mapTorsion (f : M →+ N) (n : ℕ+) : torsionLevel M n →+ torsionLevel N n where
  toFun x := ⟨f x.val, by
    change (n : ℕ) • f x.val = 0
    rw [← map_nsmul, x.property, map_zero]⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' x y := Subtype.ext (f.map_add x.val y.val)

/-- An additive map of point groups acts on all existing restricted torsion levels. -/
def map (f : M →+ N) : RestrictedTateModule M S →+ RestrictedTateModule N S :=
  mapLevels (fun n => mapTorsion f n.1)
    (fun n m x => by
      apply Subtype.ext
      exact (map_nsmul f (m.1 : ℕ) (x : M)).symm)

@[simp] theorem evaluation_map (f : M →+ N) (x : RestrictedTateModule M S) (n : S) :
    evaluation N S n (map f x) = f (evaluation M S n x) := rfl

/-- Functorial maps preserve the existing inverse-limit topology. -/
theorem continuous_map (f : M →+ N) : Continuous (map (S := S) f) := by
  unfold map
  exact continuous_mapLevels _ _

/-- The functorial map in the multiplicative notation of fundamental groups. -/
def mapHom (f : M →+ N) :
    Multiplicative (RestrictedTateModule M S) →ₜ*
      Multiplicative (RestrictedTateModule N S) where
  toFun x := Multiplicative.ofAdd (map f (Multiplicative.toAdd x))
  map_one' := (map f).map_zero
  map_mul' x y := (map f).map_add x y
  continuous_toFun := continuous_map f

/-- An injection of point groups remains injective on compatible torsion families. -/
theorem mapHom_injective (f : M →+ N) (hf : Function.Injective f) :
    Function.Injective (mapHom (S := S) f) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  apply ext
  intro n
  apply hf
  exact congrArg (fun z => evaluation N S n (Multiplicative.toAdd z)) hxy


/-- Composition on the point groups gives composition on the same restricted torsion families. -/
@[simp] theorem map_comp {P : Type*} [AddCommGroup P]
    (f : M →+ N) (g : N →+ P) (x : RestrictedTateModule M S) :
    map (g.comp f) x = map g (map f x) := by
  apply ext
  intro n
  rfl

/-- An equivalence of point groups transports their original restricted Tate modules. -/
noncomputable def mapEquiv (e : M ≃+ N) :
    Multiplicative (RestrictedTateModule M S) ≃ₜ*
      Multiplicative (RestrictedTateModule N S) :=
  ProCGroups.ContinuousMulEquiv.ofHomInv (mapHom e.toAddMonoidHom)
    (mapHom e.symm.toAddMonoidHom)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change e.symm (e (evaluation M S n (Multiplicative.toAdd x))) =
        evaluation M S n (Multiplicative.toAdd x)
      exact e.symm_apply_apply _)
    (fun x => by
      apply Multiplicative.toAdd.injective
      apply ext
      intro n
      change e (e.symm (evaluation N S n (Multiplicative.toAdd x))) =
        evaluation N S n (Multiplicative.toAdd x)
      exact e.apply_symm_apply _)

/-- The point equivalence is retained on every coordinate. -/
@[simp] theorem mapEquiv_apply (e : M ≃+ N)
    (x : Multiplicative (RestrictedTateModule M S)) :
    mapEquiv e x = Multiplicative.ofAdd
      (map e.toAddMonoidHom (Multiplicative.toAdd x)) := rfl

/-- A family of additive maps continuous on each discrete torsion level acts jointly
continuously on the existing restricted inverse limit. -/
theorem continuous_map_family {T : Type*} [TopologicalSpace T] (f : T → M →+ N)
    (hf : ∀ n : S,
      let _ := FullTateModule.torsionLevelTopology M n.1
      let _ := FullTateModule.torsionLevelTopology N n.1
      Continuous (fun z : T × torsionLevel M n.1 => mapTorsion (f z.1) n.1 z.2)) :
    Continuous (fun z : T × RestrictedTateModule M S => map (f z.1) z.2) := by
  let (n : ℕ+) := FullTateModule.torsionLevelTopology M n
  let (n : ℕ+) := FullTateModule.torsionLevelTopology N n
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (hf n).comp (continuous_fst.prodMk
    ((continuous_projection M S n).comp continuous_snd))

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
