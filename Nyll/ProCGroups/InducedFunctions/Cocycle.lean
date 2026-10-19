/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InducedFunctions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Explicit cocycle primitives for induced functions

For the existing right-translation induced module, evaluation at the identity
restricts a cocycle to the subgroup. A primitive `b` of that restricted cocycle
gives the induced primitive `x ↦ f(x)(1) * b`. The same formula preserves any
pointwise integral subgroup when the cocycle values and `b` lie in it.
-/

noncomputable section

namespace ProCGroups.InducedFunctions

variable {G B : Type*} [Group G] [CommGroup B]
    (H : Subgroup G) [MulDistribMulAction H B]

/-- Restriction to the subgroup followed by evaluation gives the actual subgroup cocycle. -/
theorem induced_isMulCocycle_restrict_evaluation
    (f : G → InducedModule (B := B) H) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCocycle₁ (fun h : H => inducedEvaluation H (f h.1)) := by
  intro h k
  have hfk := congrArg (inducedEvaluation (B := B) H) (hf h.1 k.1)
  rw [map_mul, inducedEvaluation_smul] at hfk
  exact hfk

/-- The explicit induced primitive constructed from the evaluated subgroup primitive. -/
def inducedCocyclePrimitive
    (f : G → InducedModule (B := B) H) (hf : groupCohomology.IsMulCocycle₁ f)
    (b : B) (hb : ∀ h : H, (h • b) / b = inducedEvaluation H (f h.1)) :
    InducedModule (B := B) H :=
  ⟨fun x => inducedEvaluation H (f x) * b, by
    intro h x
    have hfx := congrArg (inducedEvaluation (B := B) H) (hf h.1 x)
    rw [map_mul, inducedEvaluation_smul] at hfx
    change inducedEvaluation H (f (h.1 * x)) * b =
      h • (inducedEvaluation H (f x) * b)
    rw [hfx, ← hb h, smul_mul']
    simp only [mul_assoc, div_mul_cancel]⟩

/-- The induced primitive evaluates by the concrete cocycle formula. -/
@[simp]
theorem inducedCocyclePrimitive_apply
    (f : G → InducedModule (B := B) H) (hf : groupCohomology.IsMulCocycle₁ f)
    (b : B) (hb : ∀ h : H, (h • b) / b = inducedEvaluation H (f h.1)) (x : G) :
    (inducedCocyclePrimitive H f hf b hb).1 x = inducedEvaluation H (f x) * b :=
  rfl

/-- The explicit induced primitive solves the cocycle equation for every group element. -/
theorem inducedCocyclePrimitive_coboundary
    (f : G → InducedModule (B := B) H) (hf : groupCohomology.IsMulCocycle₁ f)
    (b : B) (hb : ∀ h : H, (h • b) / b = inducedEvaluation H (f h.1)) (g : G) :
    (g • inducedCocyclePrimitive H f hf b hb) / inducedCocyclePrimitive H f hf b hb = f g := by
  apply Subtype.ext
  funext x
  have hfx := congrArg (fun z : InducedModule (B := B) H => z.1 1) (hf x g)
  change (f (x * g)).1 1 = (f g).1 (1 * x) * (f x).1 1 at hfx
  rw [one_mul] at hfx
  change ((f (x * g)).1 1 * b) / ((f x).1 1 * b) = (f g).1 x
  rw [mul_div_mul_right_eq_div, hfx, mul_div_cancel_right]

/-- Solving the evaluated subgroup cocycle solves the original induced cocycle. -/
theorem induced_isMulCoboundary_of_evaluation
    (f : G → InducedModule (B := B) H) (hf : groupCohomology.IsMulCocycle₁ f)
    (hb : groupCohomology.IsMulCoboundary₁
      (fun h : H => inducedEvaluation H (f h.1))) :
    groupCohomology.IsMulCoboundary₁ f := by
  obtain ⟨b, hb⟩ := hb
  exact ⟨inducedCocyclePrimitive H f hf b hb,
    inducedCocyclePrimitive_coboundary H f hf b hb⟩

/-- The explicit primitive preserves pointwise membership in an integral subgroup. -/
theorem inducedCocyclePrimitive_mem
    (U : Subgroup B) (f : G → InducedModule (B := B) H)
    (hf : groupCohomology.IsMulCocycle₁ f)
    (hfint : ∀ g x : G, (f g).1 x ∈ U)
    (b : B) (hb : ∀ h : H, (h • b) / b = inducedEvaluation H (f h.1))
    (hbint : b ∈ U) (x : G) :
    (inducedCocyclePrimitive H f hf b hb).1 x ∈ U :=
  U.mul_mem (hfint x 1) hbint

/-- An integral primitive at the subgroup gives an actual pointwise integral induced primitive. -/
theorem induced_exists_integral_coboundary_of_evaluation
    (U : Subgroup B) (f : G → InducedModule (B := B) H)
    (hf : groupCohomology.IsMulCocycle₁ f)
    (hfint : ∀ g x : G, (f g).1 x ∈ U)
    (hb : ∃ b : B, b ∈ U ∧
      ∀ h : H, (h • b) / b = inducedEvaluation H (f h.1)) :
    ∃ b : InducedModule (B := B) H,
      (∀ x : G, b.1 x ∈ U) ∧ ∀ g : G, (g • b) / b = f g := by
  obtain ⟨b, hbint, hb⟩ := hb
  exact ⟨inducedCocyclePrimitive H f hf b hb,
    inducedCocyclePrimitive_mem H U f hf hfint b hb hbint,
    inducedCocyclePrimitive_coboundary H f hf b hb⟩

end ProCGroups.InducedFunctions
