/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.PrimaryDetection
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualMonotonicity
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
public import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-!
# Detection by the primary and prime-to-primary quotients

A profinite abelian group injects into the product of its actual maximal
pro-p and pro-prime-to-p quotients. The residual kernels have trivial
intersection: the pro-p quotient detects the p-primary coordinate, while
every other primary quotient factors through the prime-to-p quotient.
The existing separation theorem for all primary quotients then detects the
original element. No decomposition of the group is assumed.

For an original continuous automorphism, the canonical induced quotient
automorphisms therefore detect fixed elements in the full group.
-/

@[expose] public section

namespace ProCGroups.ProC

universe u

variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The pair of the original maximal pro-p and prime-to-p projections. -/
noncomputable def primaryQuotientPair :
    A →ₜ* (A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A) ×
      (A ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A) :=
  (show A →ₜ* A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A from
    { toMonoidHom := QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A)
      continuous_toFun := QuotientGroup.continuous_mk }).prod
    { toMonoidHom := QuotientGroup.mk'
        (proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A)
      continuous_toFun := QuotientGroup.continuous_mk }

/-- Both coordinates of the canonical map retain the original representative. -/
theorem primaryQuotientPair_apply (a : A) :
    primaryQuotientPair p A a =
      (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A) a,
        QuotientGroup.mk'
          (proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A) a) := rfl

variable [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]

/-- The actual two residual cores have trivial intersection in a profinite
abelian group, proved by detection in every prime-primary quotient. -/
theorem primary_primeTo_residualCore_inf_eq_bot :
    proCResidualCore (FiniteGroupClass.pGroup p) A ⊓
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  apply Subgroup.mem_bot.mpr
  apply eq_one_of_forall_primaryQuotient a
  intro q _hq
  apply (QuotientGroup.eq_one_iff
    (N := proCResidualCore (FiniteGroupClass.pGroup q) A) a).mpr
  by_cases hqp : q = p
  · subst q
    exact ha.1
  · have hclass : ∀ {Q : Type u} [Group Q],
        FiniteGroupClass.pGroup q Q →
          FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ) Q := by
      intro Q _ hQ
      have : Finite Q := hQ.1
      obtain ⟨n, hn⟩ := hQ.2.exists_card_eq
      refine ⟨hQ.1, ?_⟩
      rw [hn]
      apply FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem
      · exact fun h => hqp (Set.mem_singleton_iff.mp h)
      · exact Fact.out
    exact proCResidualCore_antitone hclass ha.2

/-- The kernel of the canonical pair of quotient projections is trivial. -/
theorem primaryQuotientPair_ker_eq_bot :
    (primaryQuotientPair p A).toMonoidHom.ker = ⊥ := by
  rw [← primary_primeTo_residualCore_inf_eq_bot p A]
  ext a
  change primaryQuotientPair p A a = 1 ↔
    a ∈ proCResidualCore (FiniteGroupClass.pGroup p) A ∧
      a ∈ proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A
  rw [primaryQuotientPair_apply]
  change
    (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A) a,
      QuotientGroup.mk'
        (proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A) a) =
      (1, 1) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr (QuotientGroup.eq_one_iff a) (QuotientGroup.eq_one_iff a)

/-- The full profinite abelian group embeds by the original two quotient maps. -/
theorem primaryQuotientPair_injective : Function.Injective (primaryQuotientPair p A) :=
  (MonoidHom.ker_eq_bot_iff (primaryQuotientPair p A).toMonoidHom).mp
    (primaryQuotientPair_ker_eq_bot p A)

/-- Fixed vanishing on the two canonical quotients implies fixed vanishing
in the original profinite abelian group. The quotient automorphisms and their
compatibility with the original automorphism are constructed functorially. -/
theorem fixed_eq_one_of_primary_primeTo_fixed_vanishing
    (F : A ≃ₜ* A)
    (hp : ∀ a : A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A,
      residualQuotientContinuousMulEquiv (FiniteGroupClass.pGroup_hereditary p) F a = a →
        a = 1)
    (hprimeTo : ∀ a : A ⧸
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A,
      residualQuotientContinuousMulEquiv
        (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).hereditary F a = a →
        a = 1)
    {a : A} (ha : F a = a) : a = 1 := by
  apply primaryQuotientPair_injective p A
  rw [map_one, primaryQuotientPair_apply]
  apply Prod.ext
  · apply hp
    rw [residualQuotientContinuousMulEquiv_apply_mk, ha]
  · apply hprimeTo
    rw [residualQuotientContinuousMulEquiv_apply_mk, ha]

end ProCGroups.ProC
