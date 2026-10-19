/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Continuous

/-!
# Dense homomorphisms detect open subgroup inclusions

Pulling back open subgroups along a homomorphism with dense image reflects
their order. The closure of the image of each pullback contains the original
open subgroup, and open subgroups are also closed.
-/

namespace ProCGroups

variable {A B : Type*} [Group A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

/-- A dense homomorphism reflects inclusions between open subgroups. -/
theorem openSubgroup_comap_le_comap_iff (f : A →* B) (hf : DenseRange f)
    (S T : OpenSubgroup B) :
    S.toSubgroup.comap f ≤ T.toSubgroup.comap f ↔ S ≤ T := by
  constructor
  · intro h
    have hi : f '' (f ⁻¹' (S : Set B)) ⊆ (T : Set B) := by
      rintro _ ⟨a, ha, rfl⟩
      exact h ha
    exact (hf.subset_closure_image_preimage_of_isOpen S.isOpen').trans
      (closure_minimal hi T.isClosed)
  · intro h a ha
    exact h ha

end ProCGroups
