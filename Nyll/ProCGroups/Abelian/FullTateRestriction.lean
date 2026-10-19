/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.RestrictedTateModule
import Nyll.ProCGroups.Abelian.FullTateModuleMap

/-!
# Restriction and detection of actual full Tate families

Restriction retains the original coordinates. Vanishing on the powers of
each positive integer detects vanishing of the full compatible family.
-/

namespace ProCGroups.FullTateModule

variable (M : Type*) [AddCommGroup M] (S : Submonoid ℕ+)

/-- Restrict the actual full compatible family to a multiplicative index set. -/
def restrict : FullTateModule M →+ RestrictedTateModule M S where
  toFun x := ⟨fun n => projection M n.1 x, fun n m => x.2 n.1 m.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evaluation_restrict (x : FullTateModule M) (n : S) :
    RestrictedTateModule.evaluation M S n (restrict M S x) =
      evaluation M n.1 x := rfl

/-- Restriction is continuous for the original coordinate topologies. -/
theorem continuous_restrict : Continuous (restrict M S) := by
  let (n : ℕ+) := torsionLevelTopology M n
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact continuous_projection M n.1

/-- No change of the coefficient action is introduced by restriction. -/
@[simp] theorem evaluation_restrict_map
    {N : Type*} [AddCommGroup N] (f : M →+ N)
    (x : FullTateModule M) (n : S) :
    RestrictedTateModule.evaluation N S n (restrict N S (map f x)) =
      f (evaluation M n.1 x) := rfl

/-- It suffices to kill the restriction to the powers of each arbitrary
positive integer; no fixed local place must handle all integers at once. -/
theorem eq_zero_of_restrict_powers_eq_zero (x : FullTateModule M)
    (h : ∀ n : ℕ+, restrict M (Submonoid.powers n) x = 0) : x = 0 := by
  apply ext
  intro n
  have hn : n ∈ Submonoid.powers n := ⟨1, pow_one n⟩
  have he := congrArg
    (RestrictedTateModule.evaluation M (Submonoid.powers n) ⟨n, hn⟩) (h n)
  exact he

end ProCGroups.FullTateModule
