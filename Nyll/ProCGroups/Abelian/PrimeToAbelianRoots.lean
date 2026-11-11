/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.PrimeToRootsDetection
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPowerDetection
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# Original roots characters and the canonical prime-to-p abelian quotient

Each invertible roots character factors through the original topological
abelianization and its actual maximal prime-to-p residual quotient. The
same characters jointly detect the kernel of that canonical composition.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

open ProCGroups.ProC

universe u v

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical original map to the maximal prime-to-p quotient of the
full topological abelianization. -/
def primeToAbelianMk :
    G →ₜ* TopologicalAbelianization G ⧸
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ))
        (TopologicalAbelianization G) :=
  (show TopologicalAbelianization G →ₜ* _ from
    { toMonoidHom := QuotientGroup.mk' _
      continuous_toFun := QuotientGroup.continuous_mk }).comp
        (TopologicalAbelianization.mkₜ G)

/-- The canonical composition is surjective on original representatives. -/
theorem primeToAbelianMk_surjective : Function.Surjective (primeToAbelianMk p G) :=
  (QuotientGroup.mk'_surjective _).comp (TopologicalAbelianization.surjective_mk G)

variable {G} (K : Type v) [Field K] [IsSepClosed K] [Fact p.Prime] [CharP K p]

/-- Every original character with invertible roots coefficients descends
through the actual canonical prime-to-p abelian quotient. -/
def primeToAbelianRootsLift
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    [TopologicalSpace (rootsOfUnity (n : ℕ) K)]
    [DiscreteTopology (rootsOfUnity (n : ℕ) K)]
    (χ : G →ₜ* rootsOfUnity (n : ℕ) K) :
    TopologicalAbelianization G ⧸
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ))
        (TopologicalAbelianization G) →ₜ* rootsOfUnity (n : ℕ) K := by
  have hs : FiniteGroupClass.IsSigmaNumber ({p}ᶜ : Set ℕ) (n : ℕ) := by
    intro q _hq hq hdiv
    have hqp : q = p := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hq
    subst q
    exact hn.ne_zero ((CharP.cast_eq_zero_iff K p (n : ℕ)).mpr hdiv)
  exact QuotientGroup.liftₜ _ (TopologicalAbelianization.lift χ)
    (proCResidualCore_le_ker_of_finite_exponent ({p}ᶜ : Set ℕ)
      (TopologicalAbelianization.lift χ) (n : ℕ) hs (fun z => Subtype.ext z.property))

omit [IsSepClosed K] [Fact p.Prime] in
/-- The descended character evaluates the same original representative. -/
theorem primeToAbelianRootsLift_apply_mk
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    [TopologicalSpace (rootsOfUnity (n : ℕ) K)]
    [DiscreteTopology (rootsOfUnity (n : ℕ) K)]
    (χ : G →ₜ* rootsOfUnity (n : ℕ) K) (g : G) :
    primeToAbelianRootsLift p K n hn χ (primeToAbelianMk p G g) = χ g := rfl

omit [IsSepClosed K] [Fact p.Prime] in
/-- Equality in the actual quotient implies equality of each original
invertible roots character, with no chosen coefficient identification. -/
theorem unit_roots_character_eq_of_primeToAbelianMk_eq
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    [TopologicalSpace (rootsOfUnity (n : ℕ) K)]
    [DiscreteTopology (rootsOfUnity (n : ℕ) K)]
    (χ : G →ₜ* rootsOfUnity (n : ℕ) K) {g h : G}
    (hgh : primeToAbelianMk p G g = primeToAbelianMk p G h) : χ g = χ h :=
  congrArg (primeToAbelianRootsLift p K n hn χ) hgh

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The kernel of the canonical prime-to-p abelian quotient is exactly
the common kernel of all original invertible roots characters. -/
theorem primeToAbelianMk_eq_one_iff_unit_roots_characters (g : G) :
    primeToAbelianMk p G g = 1 ↔
      ∀ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K)),
        let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
        let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
        ∀ χ : G →ₜ* rootsOfUnity (n : ℕ) K, χ g = 1 := by
  constructor
  · intro hg n hn top disc χ
    have h := congrArg (primeToAbelianRootsLift p K n hn χ) hg
    exact h.trans (map_one _)
  · intro hg
    let A := TopologicalAbelianization G
    let R := proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A
    have : TotallyDisconnectedSpace A :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
        (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
    have : IsClosed (R : Set A) := proCResidualCore_isClosed _ _
    apply eq_one_of_unit_roots_characters K p
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (FiniteGroupClass.sigmaGroup_formation ({p}ᶜ : Set ℕ))) (primeToAbelianMk p G g)
    intro n hn top disc χ
    exact hg n hn (χ.comp (primeToAbelianMk p G))

end ProCGroups.Abelian
