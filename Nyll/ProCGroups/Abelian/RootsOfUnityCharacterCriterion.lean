/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.ProCGroups.Abelian.FiniteCharacterCriterion
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Circle
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualFiniteDescent
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPowerDetection
public import Mathlib.GroupTheory.Index
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Roots of unity detect profinite abelian isomorphisms

A finite subgroup of the circle is cyclic. Its order identifies it with the
actual roots of unity of a separably closed characteristic-zero field.
Transporting characters along this finite coefficient isomorphism reduces
isomorphism detection to roots-of-unity coefficients.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Duality

theorem bijective_compLeft_of_coefficient_equiv
    {G H A B : Type*} [Group G] [Group H] [CommGroup A] [CommGroup B]
    [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B]
    (f : G →ₜ* H) (e : A ≃ₜ* B)
    (h : Function.Bijective (f.compLeft A)) : Function.Bijective (f.compLeft B) := by
  constructor
  · intro χ ψ hχψ
    have hh : (e.symm : B →ₜ* A).comp χ =
        (e.symm : B →ₜ* A).comp ψ := by
      apply h.injective
      exact congrArg (fun z : G →ₜ* B => (e.symm : B →ₜ* A).comp z) hχψ
    apply ContinuousMonoidHom.ext
    intro x
    apply e.symm.injective
    exact congrArg (fun z : H →ₜ* A => z x) hh
  · intro χ
    obtain ⟨ψ, hψ⟩ := h.surjective ((e.symm : B →ₜ* A).comp χ)
    refine ⟨(e : A →ₜ* B).comp ψ, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have hx := congrArg (fun z : G →ₜ* A => z x) hψ
    change ψ (f x) = e.symm (χ x) at hx
    change e (ψ (f x)) = χ x
    rw [hx, e.apply_symm_apply]

/-- Roots of unity over a separably closed characteristic-zero field suffice
as finite coefficients for detecting a profinite abelian isomorphism. -/
def equivOfBijectiveRootsOfUnityPullback
    (K : Type*) [Field K] [IsSepClosed K] [CharZero K]
    {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [CompactSpace G] [CompactSpace H]
    [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]
    (f : G →ₜ* H)
    (hf : ∀ n : ℕ+, let _ : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥;
      let _ : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩;
      Function.Bijective (f.compLeft (rootsOfUnity (n : ℕ) K))) : G ≃ₜ* H := by
  apply equivOfBijectiveFiniteCharacterPullback f
  intro A hA
  have : IsCyclic A := isCyclic_of_injective_ringHom (Circle.coeHom.comp A.subtype)
    (Circle.coe_injective.comp Subtype.val_injective)
  let n : ℕ+ := ⟨Nat.card A, Nat.card_pos⟩
  let _ : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let _ : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let e : rootsOfUnity (n : ℕ) K ≃* A :=
    mulEquivOfCyclicCardEq (HasEnoughRootsOfUnity.natCard_rootsOfUnity K (n : ℕ))
  let eTop : rootsOfUnity (n : ℕ) K ≃ₜ* A :=
    { toMulEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact bijective_compLeft_of_coefficient_equiv f eTop (hf n)

section Sigma

open ProCGroups.ProC

universe u

variable {G H : Type u} [CommGroup G] [CommGroup H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [CompactSpace H] [T2Space G] [T2Space H]
  [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]

omit [T2Space G] in
/-- A character of an actual pro-Sigma group has finite Sigma image. -/
theorem exists_finite_sigma_character_range (sigma : Set ℕ)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (χ : PontryaginDual G) :
    ∃ (A : Subgroup Circle) (_ : Finite A),
      FiniteGroupClass.IsSigmaNumber sigma (Nat.card A) ∧
        ∃ χA : G →ₜ* A, ∀ g : G, (χA g : Circle) = χ g := by
  obtain ⟨U, hU⟩ := exists_openNormal_le_character_ker χ
  let Q := G ⧸ (U : Subgroup G)
  let q : G →ₜ* Q := OpenNormalSubgroup.quotientProj U
  let χQ : Q →ₜ* Circle := ProCGroups.QuotientGroup.liftₜ (U : Subgroup G) χ hU
  let A : Subgroup Circle := χQ.toMonoidHom.range
  have : Finite A := Finite.of_surjective χQ.toMonoidHom.rangeRestrict
    χQ.toMonoidHom.rangeRestrict_surjective
  have hA : FiniteGroupClass.IsSigmaNumber sigma (Nat.card A) :=
    (hG.quotient_mem (FiniteGroupClass.sigmaGroup_formation sigma) U).2.of_dvd
      (Subgroup.card_range_dvd χQ.toMonoidHom)
  let χAQ : Q →ₜ* A :=
    { toMonoidHom := χQ.toMonoidHom.rangeRestrict
      continuous_toFun := continuous_of_discreteTopology }
  exact ⟨A, inferInstance, hA, χAQ.comp q, fun _ => rfl⟩

omit [T2Space G] [T2Space H] in
/-- Sigma-valued finite characters suffice to detect a map between actual
pro-Sigma abelian groups. Every circle character is reduced to its own image. -/
theorem bijective_character_pullback_of_sigma (sigma : Set ℕ)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) H)
    (f : G →ₜ* H)
    (hf : ∀ (A : Subgroup Circle) [Finite A],
      FiniteGroupClass.IsSigmaNumber sigma (Nat.card A) →
        Function.Bijective (f.compLeft A)) :
    Function.Bijective (PontryaginDual.map f) := by
  constructor
  · apply (injective_iff_map_eq_one (PontryaginDual.map f)).mpr
    intro χ hχ
    obtain ⟨A, hA, hAsigma, χA, hχA⟩ := exists_finite_sigma_character_range sigma hH χ
    have hcomp : f.compLeft A χA = 1 := by
      apply ContinuousMonoidHom.ext
      intro g
      apply Subtype.ext
      change (χA (f g) : Circle) = 1
      rw [hχA]
      exact congrArg (fun ψ : PontryaginDual G => ψ g) hχ
    have hzero : χA = 1 :=
      (hf A hAsigma).injective (hcomp.trans (map_one (f.compLeft A)).symm)
    apply PontryaginDual.ext
    intro g
    rw [← hχA, hzero]
    rfl
  · intro χ
    obtain ⟨A, hA, hAsigma, χA, hχA⟩ := exists_finite_sigma_character_range sigma hG χ
    obtain ⟨ψ, hψ⟩ := (hf A hAsigma).surjective χA
    let i : A →ₜ* Circle :=
      { toMonoidHom := A.subtype
        continuous_toFun := continuous_subtype_val }
    refine ⟨i.comp ψ, ?_⟩
    apply PontryaginDual.ext
    intro g
    have hh : ψ (f g) = χA g := congrArg (fun z : G →ₜ* A => z g) hψ
    exact (congrArg Subtype.val hh).trans (hχA g)

/-- Roots of unity at invertible Sigma-indices detect the actual map between
pro-Sigma abelian groups, without requiring characteristic zero. -/
def equivOfBijectiveSigmaRootsOfUnityPullback
    (K : Type*) [Field K] [IsSepClosed K] (sigma : Set ℕ)
    (hI : ∀ n : sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) H)
    (f : G →ₜ* H)
    (hf : ∀ n : sigmaTorsionIndices sigma,
      let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
      let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n.val : ℕ) K))) : G ≃ₜ* H := by
  apply equivOfBijectiveCharacterPullback f
  apply bijective_character_pullback_of_sigma sigma hG hH f
  intro A hA hAsigma
  have : IsCyclic A := isCyclic_of_injective_ringHom (Circle.coeHom.comp A.subtype)
    (Circle.coe_injective.comp Subtype.val_injective)
  let n : sigmaTorsionIndices sigma := ⟨⟨Nat.card A, Nat.card_pos⟩, hAsigma⟩
  have : NeZero ((n.val : ℕ) : K) := ⟨(hI n).ne_zero⟩
  let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
  let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
  let e : rootsOfUnity (n.val : ℕ) K ≃* A :=
    mulEquivOfCyclicCardEq (HasEnoughRootsOfUnity.natCard_rootsOfUnity K (n.val : ℕ))
  let eTop : rootsOfUnity (n.val : ℕ) K ≃ₜ* A :=
    { toMulEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact bijective_compLeft_of_coefficient_equiv f eTop (hf n)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Every finite Sigma-order roots-of-unity character descends uniquely
through the original pro-Sigma residual quotient. -/
theorem residualRootsOfUnityPullback_bijective
    (K : Type*) [Field K] (sigma : Set ℕ) (n : sigmaTorsionIndices sigma) :
    let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
    let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
    Function.Bijective
      ((ProCGroups.ContinuousMonoidHom.quotientMk
        (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G)).compLeft
          (rootsOfUnity (n.val : ℕ) K)) := by
  intro htop hdiscrete
  have : NeZero (n.val : ℕ) := ⟨n.val.ne_zero⟩
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  constructor
  · intro χ ψ h
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
    exact congrArg (fun z : G →ₜ* rootsOfUnity (n.val : ℕ) K => z g) h
  · intro χ
    have hpow (ζ : rootsOfUnity (n.val : ℕ) K) : ζ ^ (n.val : ℕ) = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact (mem_rootsOfUnity' (n.val : ℕ) _).mp ζ.property
    have hker : R ≤ χ.toMonoidHom.ker :=
      proCResidualCore_le_ker_of_finite_exponent sigma χ (n.val : ℕ) n.property hpow
    refine ⟨ProCGroups.QuotientGroup.liftₜ R χ hker, ?_⟩
    apply ContinuousMonoidHom.ext
    intro g
    rfl

/-- The original map induces an isomorphism of pro-Sigma residual quotients
when its actual Sigma-order character pullbacks are bijective. -/
def residualEquivOfBijectiveSigmaRootsOfUnityPullback
    (K : Type*) [Field K] [IsSepClosed K] (sigma : Set ℕ)
    (hI : ∀ n : sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))
    (f : G →ₜ* H)
    (hf : ∀ n : sigmaTorsionIndices sigma,
      let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
      let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n.val : ℕ) K))) :
    (G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G) ≃ₜ*
      (H ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) H) := by
  let C := FiniteGroupClass.sigmaGroup sigma
  have hC := (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary
  let RG := proCResidualCore C G
  let RH := proCResidualCore C H
  have : IsClosed (RG : Set G) := proCResidualCore_isClosed C G
  have : IsClosed (RH : Set H) := proCResidualCore_isClosed C H
  have : TotallyDisconnectedSpace (G ⧸ RG) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal RG ‹IsClosed (RG : Set G)›
  have : TotallyDisconnectedSpace (H ⧸ RH) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal RH ‹IsClosed (RH : Set H)›
  let qG := ProCGroups.ContinuousMonoidHom.quotientMk RG
  let qH := ProCGroups.ContinuousMonoidHom.quotientMk RH
  let m := residualQuotientMap hC f
  apply equivOfBijectiveSigmaRootsOfUnityPullback K sigma hI
    (proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.sigmaGroup_formation sigma))
    (proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.sigmaGroup_formation sigma)) m
  intro n htop hdiscrete
  let B := rootsOfUnity (n.val : ℕ) K
  have hG := residualRootsOfUnityPullback_bijective (G := G) K sigma n
  have hH := residualRootsOfUnityPullback_bijective (G := H) K sigma n
  have hsquare : qG.compLeft B ∘ m.compLeft B = f.compLeft B ∘ qH.compLeft B := by
    funext χ
    apply ContinuousMonoidHom.ext
    intro g
    rfl
  have hb := (hf n).comp hH
  rw [← hsquare] at hb
  exact (Function.Bijective.of_comp_iff' hG _).mp hb

/-- The Sigma equivalence retains the original map on quotient representatives. -/
@[simp] theorem residualEquivOfBijectiveSigmaRootsOfUnityPullback_apply_mk
    (K : Type*) [Field K] [IsSepClosed K] (sigma : Set ℕ)
    (hI : ∀ n : sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))
    (f : G →ₜ* H)
    (hf : ∀ n : sigmaTorsionIndices sigma,
      let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
      let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n.val : ℕ) K))) (g : G) :
    residualEquivOfBijectiveSigmaRootsOfUnityPullback K sigma hI f hf
        (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G) g) =
      QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) H) (f g) := rfl

end Sigma

end ProCGroups.Duality
