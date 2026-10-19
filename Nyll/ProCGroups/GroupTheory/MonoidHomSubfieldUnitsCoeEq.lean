/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Monoid Hom exists subfield units coe eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_exists_subfield_units_coe_eq

theorem _root_.MonoidHom.exists_subfield_units_coe_eq
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by
  let u : G → G → (↥K)ˣ := fun α β =>
    Units.mk0 (⟨(F α β : L), hF α β⟩ : K)
      (fun hzero => (F α β).ne_zero (congrArg ((↑) : K → L) hzero))
  have hu : ∀ α β, (((u α β : (↥K)ˣ) : ↥K) : L) = F α β := fun _ _ => rfl
  let F' : G →* G →* (↥K)ˣ :=
    { toFun := fun α =>
        { toFun := u α
          map_one' := by
            apply Units.ext
            apply Subtype.ext
            change ((F α 1 : Lˣ) : L) = 1
            rw [map_one, Units.val_one]
          map_mul' := by
            intro β₁ β₂
            apply Units.ext
            apply Subtype.ext
            change ((F α (β₁ * β₂) : Lˣ) : L) = (F α β₁ : L) * (F α β₂ : L)
            rw [map_mul, Units.val_mul] }
      map_one' := by
        apply MonoidHom.ext
        intro β
        apply Units.ext
        apply Subtype.ext
        change ((F 1 β : Lˣ) : L) = 1
        rw [map_one]
        rfl
      map_mul' := by
        intro α₁ α₂
        apply MonoidHom.ext
        intro β
        apply Units.ext
        apply Subtype.ext
        change ((F (α₁ * α₂) β : Lˣ) : L) = (F α₁ β : L) * (F α₂ β : L)
        rw [map_mul]
        exact Units.val_mul (F α₁ β) (F α₂ β) }
  exact ⟨F', hu⟩
end AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_exists_subfield_units_coe_eq
end ProofImplementation
