/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.ProCGroups.Abelian.CharacterDetection
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

/-!
# Torsion-freeness from finite character cardinalities

If the n-torsion levels of an abelian group have cardinality n^d for every
positive n, multiplication between its torsion levels is surjective. Applied
to the actual finite-order characters of a profinite abelian group, this
implies torsion-freeness. This criterion is designed to use geometric finite
H1 cardinality formulas directly, without assuming a free presentation.
-/

noncomputable section
namespace ProCGroups

/-- Exact torsion-level cardinalities force surjectivity of multiplication. -/
theorem torsionTransition_surjective_of_card
    {M : Type*} [AddCommGroup M] (d : ℕ)
    (hc : ∀ k : ℕ+, Nat.card (torsionLevel M k) = (k : ℕ) ^ d)
    (n m : ℕ+) : Function.Surjective (torsionTransition M n m) := by
  have hfin (k : ℕ+) : Finite (torsionLevel M k) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ k.ne_zero)
  have : Finite (torsionLevel M (n * m)) := hfin _
  have : Finite (torsionLevel M n) := hfin _
  have : Finite (torsionLevel M m) := hfin _
  let f : torsionLevel M (n * m) →+ torsionLevel M n := torsionTransition M n m
  let j : f.ker → torsionLevel M m := fun x =>
    ⟨x.val.val, congrArg (fun z : torsionLevel M n => z.val) x.property⟩
  have hj : Function.Injective j := by
    intro x y h
    have hv : x.val.val = y.val.val :=
      congrArg (fun z : torsionLevel M m => z.val) h
    exact Subtype.ext (Subtype.ext hv)
  apply AddMonoidHom.surjective_of_card_ker_le_div f
  calc
    Nat.card f.ker ≤ Nat.card (torsionLevel M m) := Nat.card_le_card_of_injective j hj
    _ = (m : ℕ) ^ d := hc m
    _ = Nat.card (torsionLevel M (n * m)) / Nat.card (torsionLevel M n) := by
      rw [hc, hc, PNat.mul_coe, mul_pow, Nat.mul_div_cancel_left]
      exact pow_pos n.pos d

/-- Finite cyclic characters over an algebraically closed field separate
the points of an actual profinite abelian group. -/
theorem eq_one_of_rootsOfUnity_characters
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (g : G)
    (hg : ∀ (n : ℕ+) [TopologicalSpace (rootsOfUnity (n : ℕ) K)]
      [DiscreteTopology (rootsOfUnity (n : ℕ) K)],
      ∀ χ : G →ₜ* rootsOfUnity (n : ℕ) K, χ g = 1) : g = 1 := by
  classical
  by_contra hne
  obtain ⟨U, hU⟩ := ProC.exists_openNormalSubgroup_not_mem hne
  let Q := G ⧸ (U : Subgroup G)
  let q : G →ₜ* Q := ProC.OpenNormalSubgroup.quotientProj U
  obtain ⟨ι, instι, a, ha, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  have hq : q g = 1 := by
    apply e.injective
    apply funext
    intro i
    have : NeZero (a i) := ⟨ne_of_gt (lt_trans Nat.zero_lt_one (ha i))⟩
    let n : ℕ+ := ⟨a i, lt_trans Nat.zero_lt_one (ha i)⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let c : rootsOfUnity (n : ℕ) K ≃* Multiplicative (ZMod (a i)) :=
      mulEquivOfCyclicCardEq (by
        rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity K (n : ℕ)]
        simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, n]
        rfl)
    let φ : Q →ₜ* rootsOfUnity (n : ℕ) K :=
      ⟨c.symm.toMonoidHom.comp
        ((Pi.evalMonoidHom (fun j => Multiplicative (ZMod (a j))) i).comp e.toMonoidHom),
        continuous_of_discreteTopology⟩
    have h := congrArg c (hg n (φ.comp q))
    change c (c.symm (e (q g) i)) = c 1 at h
    rw [c.apply_symm_apply, map_one] at h
    exact h.trans (congrArg (fun z => z i) (map_one e)).symm
  exact hU ((QuotientGroup.eq_one_iff (N := (U : Subgroup G)) g).mp hq)

private theorem character_nsmul_zero_iff
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup A]
    (χ : G →ₜ* A) (n : ℕ) :
    n • Additive.ofMul χ = 0 ↔ ∀ g, χ g ^ n = 1 := by
  constructor
  · intro h g
    have hp := congrArg (fun x : Additive (G →ₜ* A) => x.toMul g) h
    change (χ ^ n) g = 1 at hp
    rw [ContinuousMonoidHom.pow_apply] at hp
    exact hp
  · intro h
    apply Additive.toMul.injective
    change χ ^ n = 1
    apply ContinuousMonoidHom.ext
    intro g
    change (χ ^ n) g = 1
    rw [ContinuousMonoidHom.pow_apply]
    exact h g

private def torsionCharacterEquiv
    (K : Type*) [Field K] [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]
    {G : Type*} [Group G] [TopologicalSpace G] (n : ℕ+) :
    torsionLevel (Additive (G →ₜ* Kˣ)) n ≃ (G →ₜ* rootsOfUnity (n : ℕ) K) :=
  { toFun := fun φ =>
      { toMonoidHom :=
          { toFun := fun g => ⟨φ.val.toMul g, by
              exact (character_nsmul_zero_iff φ.val.toMul (n : ℕ)).mp φ.property g⟩
            map_one' := Subtype.ext φ.val.toMul.map_one
            map_mul' := fun g h => Subtype.ext (φ.val.toMul.map_mul g h) }
        continuous_toFun := Continuous.subtype_mk φ.val.toMul.continuous
          (fun g => (character_nsmul_zero_iff φ.val.toMul (n : ℕ)).mp φ.property g) }
    invFun := fun χ =>
      ⟨Additive.ofMul
        ({ toMonoidHom := (rootsOfUnity (n : ℕ) K).subtype.comp χ.toMonoidHom
           continuous_toFun := continuous_subtype_val.comp χ.continuous } : G →ₜ* Kˣ), by
        exact (character_nsmul_zero_iff _ (n : ℕ)).mpr
          (fun g => (χ g).property)⟩
    left_inv := by
      intro φ
      apply Subtype.ext
      apply ContinuousMonoidHom.ext
      intro g
      rfl
    right_inv := by
      intro χ
      apply ContinuousMonoidHom.ext
      intro g
      apply Subtype.ext
      rfl }

/-- The geometric cardinality pattern n^d for finite characters implies
torsion-freeness, without assuming a topological finite-rank presentation. -/
theorem isMulTorsionFree_of_rootsOfUnity_character_card
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (d : ℕ)
    (hc : ∀ (n : ℕ+) [TopologicalSpace (rootsOfUnity (n : ℕ) K)]
      [DiscreteTopology (rootsOfUnity (n : ℕ) K)],
      Nat.card (G →ₜ* rootsOfUnity (n : ℕ) K) = (n : ℕ) ^ d) :
    IsMulTorsionFree G :=
  let _ : TopologicalSpace Kˣ := ⊥
  let _ : DiscreteTopology Kˣ := ⟨rfl⟩
  let D : Type _ := Additive (G →ₜ* Kˣ)
  by
  have hD (n : ℕ+) : Nat.card (torsionLevel D n) = (n : ℕ) ^ d :=
      (Nat.card_congr (torsionCharacterEquiv K (G := G) n)).trans (hc n)
  apply (isMulTorsionFree_iff_not_isOfFinOrder (G := G)).mpr
  intro g hne hfin
  apply hne
  apply eq_one_of_rootsOfUnity_characters K g
  intro n htop hdiscrete χ
  let χu : G →ₜ* Kˣ :=
    { toMonoidHom := (rootsOfUnity (n : ℕ) K).subtype.comp χ.toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology :
        Continuous (fun z : rootsOfUnity (n : ℕ) K => (z : Kˣ))).comp χ.continuous }
  let x : torsionLevel D n := ⟨Additive.ofMul χu, by
    exact (character_nsmul_zero_iff χu (n : ℕ)).mpr
      (fun a => (χ a).property)⟩
  let m : ℕ+ := ⟨orderOf g, hfin.orderOf_pos⟩
  obtain ⟨y, hy⟩ := torsionTransition_surjective_of_card d hD n m x
  have hpoint := congrArg (fun z : torsionLevel D n => z.val.toMul g) hy
  change (((m : ℕ) • y.val).toMul g) = χu g at hpoint
  rw [toMul_nsmul, ContinuousMonoidHom.pow_apply] at hpoint
  apply Subtype.ext
  change χu g = 1
  rw [← hpoint, ← map_pow]
  change y.val.toMul (g ^ orderOf g) = 1
  rw [pow_orderOf_eq_one, map_one]

end ProCGroups
