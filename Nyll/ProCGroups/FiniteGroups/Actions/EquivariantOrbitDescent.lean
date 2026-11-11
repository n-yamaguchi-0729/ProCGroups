/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Descent of an equivariant equivalence to the actual orbit bases

If the fibers of two specified surjections are exactly the group orbits,
an equivariant equivalence induces a unique equivalence of their actual
bases. The map is constructed from lifts and its independence of the lift
is proved by transitivity. No identification with a separately chosen
orbit quotient is required.
-/

@[expose] public section

noncomputable section

namespace ProCGroups

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- An equivariant equivalence descends uniquely through the specified
surjections whose fibers are the actual group orbits. -/
theorem exists_unique_equiv_of_equivariant_fibers
    {G₁ : Type u₁} {G₂ : Type u₂} [Group G₁] [Group G₂]
    {X₁ : Type v₁} {X₂ : Type v₂} [MulAction G₁ X₁] [MulAction G₂ X₂]
    {B₁ : Type w₁} {B₂ : Type w₂}
    (e : G₁ ≃* G₂) (F : X₁ ≃ X₂)
    (b₁ : X₁ → B₁) (b₂ : X₂ → B₂)
    (hs₁ : Function.Surjective b₁) (hs₂ : Function.Surjective b₂)
    (hb₁ : ∀ (g : G₁) (x : X₁), b₁ (g • x) = b₁ x)
    (hb₂ : ∀ (g : G₂) (x : X₂), b₂ (g • x) = b₂ x)
    (ho₁ : ∀ x y, b₁ x = b₁ y → ∃ g : G₁, g • x = y)
    (ho₂ : ∀ x y, b₂ x = b₂ y → ∃ g : G₂, g • x = y)
    (hF : ∀ g x, F (g • x) = e g • F x) :
    ∃! f : B₁ ≃ B₂, ∀ x, f (b₁ x) = b₂ (F x) := by
  classical
  let f : B₁ → B₂ := fun b => b₂ (F (Classical.choose (hs₁ b)))
  have hf (x : X₁) : f (b₁ x) = b₂ (F x) := by
    let y := Classical.choose (hs₁ (b₁ x))
    have hy : b₁ y = b₁ x := Classical.choose_spec (hs₁ (b₁ x))
    obtain ⟨g, hg⟩ := ho₁ y x hy
    have h := congrArg (fun z => b₂ (F z)) hg
    rw [hF, hb₂] at h
    exact h
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨x, rfl⟩ := hs₁ a
    obtain ⟨y, rfl⟩ := hs₁ b
    rw [hf, hf] at hab
    obtain ⟨g, hg⟩ := ho₂ (F x) (F y) hab
    have hxy : e.symm g • x = y := by
      apply F.injective
      rw [hF, e.apply_symm_apply]
      exact hg
    exact (hb₁ (e.symm g) x).symm.trans (congrArg b₁ hxy)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨y, rfl⟩ := hs₂ b
    exact ⟨b₁ (F.symm y), (hf (F.symm y)).trans
      (congrArg b₂ (F.apply_symm_apply y))⟩
  let E := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨E, hf, ?_⟩
  intro E' hE'
  apply Equiv.ext
  intro b
  obtain ⟨x, rfl⟩ := hs₁ b
  exact (hE' x).trans (hf x).symm

end ProCGroups
