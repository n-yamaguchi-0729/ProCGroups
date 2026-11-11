/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Invertible roots characters detect the actual prime-to-p quotient

The order of an actual finite quotient is invertible in the coefficient
field. Finite abelian duality therefore supplies an actual roots-of-unity
character detecting every nonidentity element. This includes finite torsion
and uses no characteristic-zero hypothesis.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

open ProCGroups.ProC

universe u v

/-- Every nonidentity element of an abelian pro-prime-to-p group is detected
by an actual character with an invertible roots-of-unity coefficient group. -/
theorem exists_unit_roots_character_of_ne_one
    (K : Type v) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (hA : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A)
    {a : A} (ha : a ≠ 1) :
    ∃ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K)),
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
      ∃ χ : A →ₜ* rootsOfUnity (n : ℕ) K, χ a ≠ 1 := by
  obtain ⟨U, hU⟩ := hA.exists_openNormalSubgroupInClass_not_mem ha
  let Q := A ⧸ (U.1 : Subgroup A)
  have : Finite Q := U.2.1
  let n : ℕ+ := ⟨Nat.card Q, Nat.card_pos⟩
  have hn : IsUnit ((n : ℕ) : K) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact U.2.2 p (Fact.out : p.Prime) (not_not.mpr rfl)
      ((CharP.cast_eq_zero_iff K p (n : ℕ)).mp hz)
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : HasEnoughRootsOfUnity K (Monoid.exponent Q) :=
    HasEnoughRootsOfUnity.of_dvd K (n := (n : ℕ))
      (Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : Q => pow_card_eq_one' (x := x)))
  let q := ProC.OpenNormalSubgroup.quotientProj U.1
  have hq : q a ≠ 1 := by
    intro heq
    exact hU ((QuotientGroup.eq_one_iff (N := (U.1 : Subgroup A)) a).mp heq)
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q K hq
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let χ : Q →ₜ* rootsOfUnity (n : ℕ) K :=
    { toMonoidHom :=
        { toFun x := ⟨ψ x, by
            change ψ x ^ (n : ℕ) = 1
            rw [← map_pow]
            exact (congrArg ψ (pow_card_eq_one' (x := x))).trans (map_one ψ)⟩
          map_one' := Subtype.ext (map_one ψ)
          map_mul' x y := Subtype.ext (map_mul ψ x y) }
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨n, hn, χ.comp q, ?_⟩
  intro heq
  exact hψ (congrArg Subtype.val heq)

/-- Invertible roots characters detect equality to one, including all
finite torsion in an actual abelian pro-prime-to-p group. -/
theorem eq_one_of_unit_roots_characters
    (K : Type v) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (hA : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A)
    (a : A)
    (ha : ∀ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K)),
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
      ∀ χ : A →ₜ* rootsOfUnity (n : ℕ) K, χ a = 1) : a = 1 := by
  by_contra hne
  obtain ⟨n, hn, χ, hχ⟩ := exists_unit_roots_character_of_ne_one K p hA hne
  exact hχ (ha n hn χ)

end ProCGroups.Abelian
