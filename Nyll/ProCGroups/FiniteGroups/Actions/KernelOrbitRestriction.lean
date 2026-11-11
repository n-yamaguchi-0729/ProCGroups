/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FiniteGroups.Actions.KernelOrbitAction

/-!
# Kernel orbits after restriction to a subgroup containing the kernel

A restriction that contains the original kernel does not change its point
orbits. An equivariant bijection of the actual point sets therefore descends
to a bijection of the original kernel quotients. The comparison retains the
same representatives and intertwines the actual descended actions.
-/

@[expose] public section

noncomputable section

namespace ProCGroups

universe u v w z r s

variable {G : Type u} {H : Type v} {P : Type w} {Q : Type z}
  [Group G] [Group H] [Group P] [Group Q]
  (q : G →* P) (q' : H →* Q) (i : H →* G) (f : Q →* P)
  (hcomp : ∀ h, q (i h) = f (q' h)) (hf : Function.Injective f)
  (hker : ∀ g, q g = 1 → ∃ h, i h = g)
  {X : Type r} {Y : Type s} [MulAction G X] [MulAction H Y]
  (e : X ≃ Y) (he : ∀ h x, e (i h • x) = h • e x)

include hcomp hf hker he in
/-- The original kernel orbit relation is unchanged by the restriction. -/
theorem kernelOrbitRel_restriction_iff (x y : X) :
    MulAction.orbitRel q'.ker Y (e x) (e y) ↔ MulAction.orbitRel q.ker X x y := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨i h.val, ?_⟩, ?_⟩
    · exact (hcomp h.val).trans ((congrArg f h.property).trans f.map_one)
    · apply e.injective
      exact (he h.val y).trans hh
  · rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ := hker g.val g.property
    have hq' : q' h = 1 := by
      apply hf
      exact (hcomp h).symm.trans
        ((congrArg q hh).trans (g.property.trans f.map_one.symm))
    refine ⟨⟨h, hq'⟩, ?_⟩
    exact (he h y).symm.trans
      ((congrArg (fun a : G => e (a • y)) hh).trans (congrArg e hg))

/-- Restricting to a group containing the original kernel and transporting
the actual action preserves the original point-orbit quotient. -/
def kernelOrbitRestrictionEquiv : KernelOrbit q X ≃ KernelOrbit q' Y where
  toFun := Quotient.map e (fun x y h =>
    (kernelOrbitRel_restriction_iff q q' i f hcomp hf hker e he x y).mpr h)
  invFun := Quotient.map e.symm (by
    intro x y h
    apply (kernelOrbitRel_restriction_iff q q' i f hcomp hf hker e he (e.symm x) (e.symm y)).mp
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact h)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x =>
      change (Quotient.mk _ (e.symm (e x)) : KernelOrbit q X) = Quotient.mk _ x
      rw [e.symm_apply_apply]
  right_inv := by
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      change (Quotient.mk _ (e (e.symm y)) : KernelOrbit q' Y) = Quotient.mk _ y
      rw [e.apply_symm_apply]

/-- The orbit comparison uses the specified actual point bijection. -/
theorem kernelOrbitRestrictionEquiv_mk (x : X) :
    kernelOrbitRestrictionEquiv q q' i f hcomp hf hker e he (Quotient.mk _ x) =
      Quotient.mk _ (e x) := rfl

/-- Its action square uses the given quotient inclusion and original
point action, rather than a separately chosen action on the quotient. -/
theorem kernelOrbitRestrictionEquiv_smul
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (a : Q) (x : KernelOrbit q X) :
    let _ := kernelOrbitAction q X hq
    let _ := kernelOrbitAction q' Y hq'
    kernelOrbitRestrictionEquiv q q' i f hcomp hf hker e he (f a • x) =
      a • kernelOrbitRestrictionEquiv q q' i f hcomp hf hker e he x := by
  intro action action'
  obtain ⟨h, rfl⟩ := hq' a
  induction x using Quotient.inductionOn with
  | h x =>
    rw [← hcomp, kernelOrbitAction_mk, kernelOrbitRestrictionEquiv_mk,
      kernelOrbitRestrictionEquiv_mk, kernelOrbitAction_mk, he]

end ProCGroups
