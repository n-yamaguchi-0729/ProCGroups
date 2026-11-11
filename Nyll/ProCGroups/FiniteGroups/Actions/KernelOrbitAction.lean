/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Descending an actual point action through a quotient group

For a surjective group map, quotient the original point set by the action
of its actual kernel. The target group acts on these point orbits, and the
stabilizer is exactly the image of the original stabilizer. No coset model
or identification of stabilizers is supplied as a premise.
-/

@[expose] public section

noncomputable section

namespace ProCGroups

universe u v w z

variable {G : Type u} {P : Type v} [Group G] [Group P]
  (q : G →* P) (X : Type w) [MulAction G X]

/-- Orbits of the actual kernel on the original point set. -/
abbrev KernelOrbit := Quotient (MulAction.orbitRel q.ker X)

/-- The normal kernel orbit relation is preserved by the ambient action. -/
theorem kernelOrbitRel_smul (g : G) {x y : X}
    (h : MulAction.orbitRel q.ker X x y) :
    MulAction.orbitRel q.ker X (g • x) (g • y) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨⟨g * (n : G) * g⁻¹, ?_⟩, ?_⟩
  · change q (g * (n : G) * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, n.property, mul_one, mul_inv_cancel]
  · change (g * (n : G) * g⁻¹) • (g • y) = g • x
    rw [mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun t : X => g • t) hn

/-- The action of one quotient element on kernel orbits. -/
def kernelOrbitSmul (hq : Function.Surjective q) (p : P) :
    KernelOrbit q X → KernelOrbit q X :=
  Quotient.map (fun x => Function.surjInv hq p • x)
    (fun _ _ h => kernelOrbitRel_smul q X (Function.surjInv hq p) h)

/-- The quotient action agrees with the original action on representatives. -/
theorem kernelOrbitSmul_mk (hq : Function.Surjective q) (g : G) (x : X) :
    kernelOrbitSmul q X hq (q g) (Quotient.mk _ x) =
      Quotient.mk _ (g • x) := by
  apply Quotient.sound
  let s := Function.surjInv hq (q g)
  have hs : q s = q g := Function.surjInv_eq hq (q g)
  refine ⟨⟨s * g⁻¹, ?_⟩, ?_⟩
  · change q (s * g⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  · change (s * g⁻¹) • (g • x) = s • x
    rw [mul_smul, inv_smul_smul]

/-- The target quotient acts on the kernel orbits of the original action. -/
@[instance_reducible]
def kernelOrbitAction (hq : Function.Surjective q) : MulAction P (KernelOrbit q X) where
  smul := kernelOrbitSmul q X hq
  one_smul := by
    intro x
    induction x using Quotient.inductionOn with
    | h x =>
      change kernelOrbitSmul q X hq 1 (Quotient.mk _ x) = Quotient.mk _ x
      rw [← q.map_one, kernelOrbitSmul_mk, one_smul]
  mul_smul := by
    intro p r x
    obtain ⟨g, rfl⟩ := hq p
    obtain ⟨h, rfl⟩ := hq r
    induction x using Quotient.inductionOn with
    | h x =>
      change kernelOrbitSmul q X hq (q g * q h) (Quotient.mk _ x) =
        kernelOrbitSmul q X hq (q g)
          (kernelOrbitSmul q X hq (q h) (Quotient.mk _ x))
      rw [← q.map_mul, kernelOrbitSmul_mk, kernelOrbitSmul_mk,
        kernelOrbitSmul_mk, mul_smul]

/-- The descended action uses the same original representative. -/
theorem kernelOrbitAction_mk (hq : Function.Surjective q) (g : G) (x : X) :
    let _ := kernelOrbitAction q X hq
    q g • (Quotient.mk _ x : KernelOrbit q X) = Quotient.mk _ (g • x) :=
  kernelOrbitSmul_mk q X hq g x

/-- The actual stabilizer after descent is exactly the original stabilizer image. -/
theorem kernelOrbitAction_stabilizer (hq : Function.Surjective q) (x : X) :
    let _ := kernelOrbitAction q X hq
    MulAction.stabilizer P (Quotient.mk _ x : KernelOrbit q X) =
      (MulAction.stabilizer G x).map q := by
  intro action
  ext p
  obtain ⟨g, rfl⟩ := hq p
  change q g • (Quotient.mk _ x : KernelOrbit q X) = Quotient.mk _ x ↔ _
  rw [kernelOrbitAction_mk, Quotient.eq]
  constructor
  · rintro ⟨n, hn⟩
    change (n : G) • x = g • x at hn
    refine ⟨(n : G)⁻¹ * g, ?_, ?_⟩
    · change ((n : G)⁻¹ * g) • x = x
      rw [mul_smul, ← hn, inv_smul_smul]
    · rw [map_mul, map_inv, n.property, inv_one, one_mul]
  · rintro ⟨d, hd, hdg⟩
    refine ⟨⟨g * d⁻¹, ?_⟩, ?_⟩
    · change q (g * d⁻¹) = 1
      rw [map_mul, map_inv, hdg, mul_inv_cancel]
    · change (g * d⁻¹) • x = g • x
      rw [mul_smul]
      exact congrArg (fun t : X => g • t)
        ((MulAction.stabilizer G x).inv_mem hd)

/-- An invariant original base map descends to the point-orbit quotient. -/
def kernelOrbitBase {B : Type z} (b : X → B)
    (hb : ∀ (g : G) (x : X), b (g • x) = b x) : KernelOrbit q X → B :=
  Quotient.lift b (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact hb (g : G) y)

/-- The orbit base map keeps the literal original base point. -/
theorem kernelOrbitBase_mk {B : Type z} (b : X → B)
    (hb : ∀ (g : G) (x : X), b (g • x) = b x) (x : X) :
    kernelOrbitBase q X b hb (Quotient.mk _ x) = b x := rfl

section Composite

variable {Γ : Type z} [Group Γ] (r : P →* Γ)

/-- Passing from the original quotient to a further quotient enlarges the
kernel orbits through the identity on the original point set. -/
def kernelOrbitMap : KernelOrbit q X → KernelOrbit (r.comp q) X :=
  Quotient.map id (by
    intro x y h
    obtain ⟨n, hn⟩ := h
    refine ⟨⟨(n : G), ?_⟩, hn⟩
    change r (q (n : G)) = 1
    rw [n.property, map_one])

/-- The comparison retains the same original point. -/
theorem kernelOrbitMap_mk (x : X) :
    kernelOrbitMap q X r (Quotient.mk _ x) = Quotient.mk _ x := rfl

/-- Every orbit of the composite kernel has an original representative. -/
theorem kernelOrbitMap_surjective : Function.Surjective (kernelOrbitMap q X r) := by
  intro x
  obtain ⟨z, rfl⟩ := Quotient.exists_rep x
  exact ⟨Quotient.mk _ z, rfl⟩

/-- Elements of the remaining kernel preserve the composite-kernel orbit. -/
theorem kernelOrbitMap_smul_of_mem_ker (hq : Function.Surjective q)
    (p : P) (hp : p ∈ r.ker) (x : KernelOrbit q X) :
    let _ := kernelOrbitAction q X hq
    kernelOrbitMap q X r (p • x) = kernelOrbitMap q X r x := by
  intro action
  obtain ⟨g, rfl⟩ := hq p
  induction x using Quotient.inductionOn with
  | h x =>
    rw [kernelOrbitAction_mk]
    change (Quotient.mk _ (g • x) : KernelOrbit (r.comp q) X) = Quotient.mk _ x
    exact Quotient.sound ⟨⟨g, hp⟩, rfl⟩

/-- Fibres of the composite-kernel orbit map are precisely the orbits of
the remaining kernel. This does not require the original stabilizer to
surject onto the entire arithmetic group. -/
theorem kernelOrbitMap_eq_iff (hq : Function.Surjective q)
    (x y : KernelOrbit q X) :
    let _ := kernelOrbitAction q X hq
    kernelOrbitMap q X r x = kernelOrbitMap q X r y ↔
      ∃ p : r.ker, (p : P) • x = y := by
  intro action
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := Quotient.exists_rep x
    obtain ⟨z', rfl⟩ := Quotient.exists_rep y
    change (Quotient.mk _ z : KernelOrbit (r.comp q) X) = Quotient.mk _ z' at h
    obtain ⟨g, hg⟩ := Quotient.exact h
    change (g : G) • z' = z at hg
    have hgeom : q ((g : G)⁻¹) ∈ r.ker := by
      change r (q ((g : G)⁻¹)) = 1
      rw [map_inv, map_inv]
      change (r.comp q (g : G))⁻¹ = 1
      rw [g.property, inv_one]
    refine ⟨⟨q ((g : G)⁻¹), hgeom⟩, ?_⟩
    rw [kernelOrbitAction_mk]
    apply congrArg (fun t : X => (Quotient.mk _ t : KernelOrbit q X))
    rw [← hg, inv_smul_smul]
  · rintro ⟨p, hp⟩
    exact (kernelOrbitMap_smul_of_mem_ker q X r hq p p.property x).symm.trans
      (congrArg (kernelOrbitMap q X r) hp)

end Composite

end ProCGroups
