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

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Monoid Hom map transfer eq transfer comp
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_map_transfer_eq_transfer_comp

theorem _root_.MonoidHom.map_transfer_eq_transfer_comp
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
  classical
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g,
    MonoidHom.transfer_def (f.comp ϕ) (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]
end AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_map_transfer_eq_transfer_comp
end ProofImplementation
