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

import Mathlib.Algebra.Module.NatInt

/-!
# Add Monoid Hom exists nsmul eq zero and apply eq of surjective of forall ker
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker

theorem _root_.AddMonoidHom.exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f)
    (m : ℕ) (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
    (b : B) (hmb : m • b = 0) :
    ∃ a : A, m • a = 0 ∧ f a = b := by
  obtain ⟨a₀, ha₀⟩ := hf b
  have hker : f (m • a₀) = 0 := by rw [map_nsmul, ha₀, hmb]
  obtain ⟨j, hjker, hmj⟩ := hdiv (m • a₀) hker
  exact ⟨a₀ - j, by rw [smul_sub, hmj, sub_self], by rw [map_sub, ha₀, hjker, sub_zero]⟩
end AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
