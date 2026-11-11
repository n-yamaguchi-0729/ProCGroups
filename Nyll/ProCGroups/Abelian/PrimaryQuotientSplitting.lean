/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.PrimaryFixedDetection
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPrimeExclusion
public import Nyll.ProCGroups.ProC.Subgroups.Closed
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# The actual primary quotient product of a profinite abelian group

The two residual cores have closed sum. Its quotient is simultaneously
pro-p and pro-prime-to-p, hence trivial. Together with the proved trivial
intersection, this makes the original pair of quotient maps an actual
continuous product equivalence. Its original quotient actions commute
with every continuous automorphism.

Consequently fixed vanishing passes to these two particular canonical
quotients. No claim is made for arbitrary quotients of a fixed-free group.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.ProC

universe u

attribute [local instance] proCResidualCore_isClosed

variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]

/-- The original primary and complementary residual cores generate the
whole profinite abelian group. Closedness of their sum uses compactness. -/
theorem primary_primeTo_residualCore_sup_eq_top :
    proCResidualCore (FiniteGroupClass.pGroup p) A ⊔
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A = ⊤ := by
  let N := proCResidualCore (FiniteGroupClass.pGroup p) A
  let M := proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A
  let K : Subgroup A := N ⊔ M
  have hNclosed : IsClosed (N : Set A) :=
    proCResidualCore_isClosed (FiniteGroupClass.pGroup p) A
  have hMclosed : IsClosed (M : Set A) :=
    proCResidualCore_isClosed (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A
  have hNcompact : CompactSpace N := hNclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hMcompact : CompactSpace M := hMclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hKclosed : IsClosed (K : Set A) := by
    have hrange : Set.range (fun z : N × M => z.1.val * z.2.val) = (K : Set A) := by
      ext x
      constructor
      · rintro ⟨⟨a, b⟩, rfl⟩
        exact K.mul_mem ((show N ≤ K from le_sup_left) a.property)
          ((show M ≤ K from le_sup_right) b.property)
      · intro hx
        obtain ⟨a, ha, b, hb, hab⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := N) (t := M)).mp hx
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
    rw [← hrange]
    exact (isCompact_range
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))).isClosed
  have hNdisconnected : TotallyDisconnectedSpace (A ⧸ N) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal N hNclosed
  have hMdisconnected : TotallyDisconnectedSpace (A ⧸ M) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal M hMclosed
  let fN : A ⧸ N →ₜ* A ⧸ K :=
    QuotientGroup.mapₜ N K (ContinuousMonoidHom.id A) le_sup_left
  let fM : A ⧸ M →ₜ* A ⧸ K :=
    QuotientGroup.mapₜ M K (ContinuousMonoidHom.id A) le_sup_right
  have hfN : Function.Surjective fN := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
    exact ⟨QuotientGroup.mk' N a, rfl⟩
  have hfM : Function.Surjective fM := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
    exact ⟨QuotientGroup.mk' M a, rfl⟩
  have hproP : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (A ⧸ K) :=
    HasOpenNormalBasisInClass.of_surjective (FiniteGroupClass.pGroup_formation p)
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (FiniteGroupClass.pGroup_formation p)) fN hfN
  have hproPrimeTo : HasOpenNormalBasisInClass
      (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) (A ⧸ K) :=
    HasOpenNormalBasisInClass.of_surjective
      (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).melnikovFormation.formation
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).melnikovFormation.formation)
      fM hfM
  apply top_unique
  intro a _
  apply (QuotientGroup.eq_one_iff (N := K) a).mp
  exact continuousMonoidHom_eq_one_of_proP_to_proSigma p
    (sigma := ({p}ᶜ : Set ℕ)) (by exact fun h => h (Set.mem_singleton p))
    hproP hproPrimeTo (ContinuousMonoidHom.id (A ⧸ K)) (QuotientGroup.mk' K a)

/-- Both original quotient coordinates can be prescribed independently. -/
theorem primaryQuotientPair_surjective : Function.Surjective (primaryQuotientPair p A) := by
  rintro ⟨x, y⟩
  let N := proCResidualCore (FiniteGroupClass.pGroup p) A
  let M := proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective M y
  have hab : a⁻¹ * b ∈ N ⊔ M := by
    rw [primary_primeTo_residualCore_sup_eq_top p A]
    trivial
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := N) (t := M)).mp hab
  refine ⟨a * r, ?_⟩
  rw [primaryQuotientPair_apply]
  apply Prod.ext
  · change QuotientGroup.mk' N (a * r) = QuotientGroup.mk' N a
    have hrq : QuotientGroup.mk' N r = 1 := (QuotientGroup.eq_one_iff (N := N) r).mpr hr
    rw [map_mul, hrq, mul_one]
  · change QuotientGroup.mk' M (a * r) = QuotientGroup.mk' M b
    have heq : (a * r) * s = b := by
      rw [mul_assoc, hrs, mul_inv_cancel_left]
    have h := congrArg (QuotientGroup.mk' M) heq
    have hsq : QuotientGroup.mk' M s = 1 := (QuotientGroup.eq_one_iff (N := M) s).mpr hs
    rw [map_mul, hsq, mul_one] at h
    exact h

/-- The product equivalence is precisely the original pair of canonical
quotient maps, not a choice of abstract primary coordinates. -/
def primaryQuotientPairEquiv :
    A ≃ₜ* (A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A) ×
      (A ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A) :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (primaryQuotientPair p A).toMonoidHom (primaryQuotientPair p A).continuous_toFun
      ⟨primaryQuotientPair_injective p A, primaryQuotientPair_surjective p A⟩

/-- The continuous equivalence preserves the original quotient projections. -/
theorem primaryQuotientPairEquiv_apply (a : A) :
    primaryQuotientPairEquiv p A a = primaryQuotientPair p A a := rfl

omit [TotallyDisconnectedSpace A] in
/-- Every original automorphism acts through its canonical induced
automorphisms on the two original residual quotients. -/
theorem primaryQuotientPair_equivariant (F : A ≃ₜ* A) (a : A) :
    primaryQuotientPair p A (F a) =
      (residualQuotientContinuousMulEquiv (FiniteGroupClass.pGroup_hereditary p) F
        (primaryQuotientPair p A a).1,
       residualQuotientContinuousMulEquiv
        (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).hereditary F
        (primaryQuotientPair p A a).2) := by
  simp only [primaryQuotientPair_apply, residualQuotientContinuousMulEquiv_apply_mk]

/-- Fixed vanishing on the full group passes to these particular
canonical primary quotients because their original pair is a product
equivalence. This conclusion is not asserted for an arbitrary quotient. -/
theorem primary_primeTo_fixed_vanishing_of_fixed_vanishing
    (F : A ≃ₜ* A) (hF : ∀ a : A, F a = a → a = 1) :
    (∀ a : A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A,
      residualQuotientContinuousMulEquiv (FiniteGroupClass.pGroup_hereditary p) F a = a →
        a = 1) ∧
    (∀ a : A ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) A,
      residualQuotientContinuousMulEquiv
        (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).hereditary F a = a →
        a = 1) := by
  let Fp := residualQuotientContinuousMulEquiv (FiniteGroupClass.pGroup_hereditary p) F
  let Ft := residualQuotientContinuousMulEquiv
    (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ)).hereditary F
  constructor
  · intro a ha
    obtain ⟨x, hx⟩ := primaryQuotientPair_surjective p A (a, 1)
    have hfixed : F x = x := by
      apply primaryQuotientPair_injective p A
      calc
        primaryQuotientPair p A (F x) =
            (Fp (primaryQuotientPair p A x).1, Ft (primaryQuotientPair p A x).2) :=
          primaryQuotientPair_equivariant p A F x
        _ = (Fp a, Ft 1) := congrArg (fun z => (Fp z.1, Ft z.2)) hx
        _ = (a, 1) := Prod.ext ha Ft.map_one
        _ = primaryQuotientPair p A x := hx.symm
    have h := congrArg Prod.fst hx
    rw [hF x hfixed, map_one] at h
    exact h.symm
  · intro a ha
    obtain ⟨x, hx⟩ := primaryQuotientPair_surjective p A (1, a)
    have hfixed : F x = x := by
      apply primaryQuotientPair_injective p A
      calc
        primaryQuotientPair p A (F x) =
            (Fp (primaryQuotientPair p A x).1, Ft (primaryQuotientPair p A x).2) :=
          primaryQuotientPair_equivariant p A F x
        _ = (Fp 1, Ft a) := congrArg (fun z => (Fp z.1, Ft z.2)) hx
        _ = (1, a) := Prod.ext Fp.map_one ha
        _ = primaryQuotientPair p A x := hx.symm
    have h := congrArg Prod.snd hx
    rw [hF x hfixed, map_one] at h
    exact h.symm

end ProCGroups.ProC
