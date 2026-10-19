/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualFiniteDescent
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Data.Nat.Prime.Defs

/-!
# Finite-quotient descent for maximal prime-to-p quotients

For a prime `p`, the finite Sigma class with Sigma equal to the complement
of `{p}` consists exactly of the finite groups whose order is coprime to
`p`. The general residual-quotient descent criterion therefore tests the
actual maximal prime-to-p quotient using these finite groups.

This identifies the precise group-theoretic conclusion obtained once the
geometric extension step for finite Galois covers in Stacks Project,
Theorem 58.30.3 (tag `0C0R`) has been proved.
-/

namespace ProCGroups.ProC

universe u

private theorem sigmaGroup_compl_singleton_iff_coprime
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] :
    FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ) Q ↔
      Finite Q ∧ (Nat.card Q).Coprime p := by
  constructor
  · intro hQ
    have hp : p ∉ ({p}ᶜ : Set ℕ) := not_not.mpr rfl
    exact ⟨hQ.1,
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (hQ.2 p (Fact.out : p.Prime) hp)).symm⟩
  · rintro ⟨hfin, hcoprime⟩
    refine ⟨hfin, ?_⟩
    intro q _ hq hdiv
    have hqp : q = p := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hq
    subst q
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime.symm hdiv

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H]

/-- A continuous epimorphism induces a bijection on maximal prime-to-p
quotients exactly when every finite quotient of order coprime to `p`
descends uniquely and continuously along the original epimorphism. -/
theorem residualPrimeToQuotientMap_bijective_iff_finite_quotient_descent
    (p : ℕ) [Fact p.Prime] (f : G →ₜ* H) (hf : Function.Surjective f) :
    Function.Bijective (residualQuotientMap
      (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).hereditary f) ↔
      ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q],
        (Nat.card Q).Coprime p → ∀ (q : G →ₜ* Q), Function.Surjective q →
          ∃! r : H →ₜ* Q, r.comp f = q := by
  rw [residualQuotientMap_bijective_iff_finite_quotient_descent
    (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)) f hf]
  constructor
  · intro h Q _ _ _ _ hcoprime q hq
    exact h Q
      ((sigmaGroup_compl_singleton_iff_coprime p Q).mpr ⟨inferInstance, hcoprime⟩) q hq
  · intro h Q _ _ _ hQ q hq
    obtain ⟨hfin, hcoprime⟩ := (sigmaGroup_compl_singleton_iff_coprime p Q).mp hQ
    have : Finite Q := hfin
    exact h Q hcoprime q hq

end ProCGroups.ProC
