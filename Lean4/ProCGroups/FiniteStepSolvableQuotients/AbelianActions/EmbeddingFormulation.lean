import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.Abelian.FiniteInvariantQuotients
import ProCGroups.FreeProC.Characterization.EmbeddingProblems
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.FaithfulKernel

set_option autoImplicit false

/-!
# Finite abelian embedding problems

An invariant finite quotient of the abelianization of an open normal subgroup
produces an open normal subgroup of the ambient group and a proper finite
embedding problem.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian
open ProCGroups.FreeProC.Characterization

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Each automorphism in the quotient conjugation action is continuous. -/
theorem continuous_quotientConjugationTopologicalAbelianizationMap
    (N : Subgroup H) [N.Normal] (q : H ⧸ N) :
    Continuous (quotientConjugationTopologicalAbelianizationMap N q) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
  have heq :
      (quotientConjugationTopologicalAbelianizationMap N (QuotientGroup.mk' N h) :
        TopologicalAbelianization N → TopologicalAbelianization N) =
      conjugationTopologicalAbelianizationContinuousAut N h := by
    funext a
    obtain ⟨n, rfl⟩ := TopologicalAbelianization.surjective_mk N a
    exact (conjugationTopologicalAbelianizationContinuousAut_toMulAut_apply_mk N h n).symm
  rw [heq]
  exact (conjugationTopologicalAbelianizationContinuousAut N h).continuous_toFun

/-- The finite invariant quotient of the abelianization, pulled back to `N`. -/
noncomputable def invariantAbelianQuotientMap [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    (N : Subgroup H) →ₜ*
      TopologicalAbelianization (N : Subgroup H) ⧸
        (invariantOpenNormalCore
          (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
          (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
          U : Subgroup (TopologicalAbelianization (N : Subgroup H))) :=
  (ProC.OpenNormalSubgroup.quotientProj
    (invariantOpenNormalCore
      (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
      (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U)).comp
    (TopologicalAbelianization.mkₜ (N : Subgroup H))

/-- The map from `N` onto its finite invariant abelian quotient is surjective. -/
theorem invariantAbelianQuotientMap_surjective [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    Function.Surjective (invariantAbelianQuotientMap N U) :=
  (ProC.OpenNormalSubgroup.quotientProj_surjective
    (invariantOpenNormalCore
      (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
      (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U)).comp
    (TopologicalAbelianization.surjective_mk (N : Subgroup H))

/-- The kernel of the invariant quotient, regarded as an open normal subgroup of
the ambient group. Its ambient normality follows from invariance of the core. -/
noncomputable def invariantAbelianQuotientKernel [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    OpenNormalSubgroup H where
  toSubgroup := (invariantAbelianQuotientMap N U).toMonoidHom.ker.map
    (N : Subgroup H).subtype
  isOpen' := by
    exact N.isOpen'.isOpenMap_subtype_val
      ((invariantAbelianQuotientMap N U).toMonoidHom.ker : Set (N : Subgroup H))
      (ProC.OpenNormalSubgroup.ker (invariantAbelianQuotientMap N U)).isOpen'
  isNormal' := by
    refine ⟨?_⟩
    intro x hx h
    obtain ⟨n, hn, rfl⟩ := hx
    refine ⟨MulAut.conjNormal h n, ?_, ?_⟩
    · change invariantAbelianQuotientMap N U (MulAut.conjNormal h n) = 1
      apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mpr
      rw [← quotientConjugationTopologicalAbelianizationMap_mk_apply_mk]
      apply action_mem_invariantOpenNormalCore
      exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp hn
    · exact MulAut.conjNormal_apply h n

/-- The constructed ambient kernel lies in the original open normal subgroup. -/
theorem invariantAbelianQuotientKernel_le [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    (invariantAbelianQuotientKernel N U : Subgroup H) ≤ (N : Subgroup H) := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact n.property

/-- On elements of `N`, the ambient kernel is exactly the kernel of the finite
abelian quotient map. -/
theorem mem_invariantAbelianQuotientKernel_iff [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H)))
    (n : (N : Subgroup H)) :
    (n : H) ∈ invariantAbelianQuotientKernel N U ↔
      invariantAbelianQuotientMap N U n = 1 := by
  constructor
  · intro hn
    obtain ⟨m, hm, hmn⟩ := hn
    have heq : m = n := Subtype.ext hmn
    exact heq ▸ hm
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- Two elements of `N` have the same ambient quotient class exactly when they
have the same image in the invariant abelian quotient. -/
theorem invariantAbelianQuotientKernel_mk_eq_iff [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H)))
    (n m : (N : Subgroup H)) :
    QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) (n : H) =
        QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) (m : H) ↔
      invariantAbelianQuotientMap N U n = invariantAbelianQuotientMap N U m := by
  change ((n : H) : H ⧸ (invariantAbelianQuotientKernel N U : Subgroup H)) =
      ((m : H) : H ⧸ (invariantAbelianQuotientKernel N U : Subgroup H)) ↔ _
  rw [QuotientGroup.eq]
  change ((n⁻¹ * m : (N : Subgroup H)) : H) ∈ invariantAbelianQuotientKernel N U ↔ _
  rw [mem_invariantAbelianQuotientKernel_iff, map_mul, map_inv, inv_mul_eq_one]

/-- The finite quotient map from `N` intertwines conjugation and the induced
finite action. -/
theorem invariantAbelianQuotientMap_conj [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H)))
    (h : H) (n : (N : Subgroup H)) :
    invariantAbelianQuotientMap N U (MulAut.conjNormal h n) =
      invariantOpenNormalQuotientAction
        (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
        (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U
        (QuotientGroup.mk' (N : Subgroup H) h) (invariantAbelianQuotientMap N U n) := by
  change QuotientGroup.mk'
      (invariantOpenNormalCore
        (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
        (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U :
        Subgroup (TopologicalAbelianization (N : Subgroup H)))
      (TopologicalAbelianization.mk (N : Subgroup H) (MulAut.conjNormal h n)) = _
  rw [← quotientConjugationTopologicalAbelianizationMap_mk_apply_mk]
  exact (invariantOpenNormalQuotientAction_apply_mk
    (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
    (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U
    (QuotientGroup.mk' (N : Subgroup H) h)
    (TopologicalAbelianization.mk (N : Subgroup H) n)).symm

/-- The image of `N` in the ambient finite quotient is abelian. -/
theorem invariantAbelianQuotientKernel_commute [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H)))
    (n m : (N : Subgroup H)) :
    Commute
      (QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) (n : H))
      (QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) (m : H)) := by
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul]
  apply (invariantAbelianQuotientKernel_mk_eq_iff N U (n * m) (m * n)).mpr
  rw [map_mul, map_mul, mul_comm]

/-- Faithfulness on the finite abelian quotient forces every element whose
ambient quotient class centralizes the image of `N` to belong to `N`. -/
theorem mem_of_invariantAbelianQuotientKernel_centralizes [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H)))
    (hfaithful : Function.Injective (invariantOpenNormalQuotientAction
      (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
      (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) U))
    (h : H)
    (hcentralizes : ∀ n : (N : Subgroup H), Commute
      (QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) h)
      (QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H) (n : H))) :
    h ∈ N := by
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup H)) h).mp
  apply hfaithful
  rw [map_one]
  apply MulEquiv.ext
  intro a
  obtain ⟨n, rfl⟩ := invariantAbelianQuotientMap_surjective N U a
  rw [MulAut.one_apply]
  refine (invariantAbelianQuotientMap_conj N U h n).symm.trans ?_
  apply (invariantAbelianQuotientKernel_mk_eq_iff N U (MulAut.conjNormal h n) n).mp
  change QuotientGroup.mk' (invariantAbelianQuotientKernel N U : Subgroup H)
    (h * (n : H) * h⁻¹) = _
  rw [map_mul, map_mul, map_inv, (hcentralizes n).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- A faithful action on `N`'s topological abelianization yields an open normal
`R ≤ N` such that `N/R` is abelian and is its own centralizer in `H/R`. -/
theorem exists_openNormal_abelian_selfCentralizing_quotient
    [CompactSpace H] [TotallyDisconnectedSpace H]
    (N : OpenNormalSubgroup H)
    (hfaithful : Function.Injective
      (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))) :
    ∃ R : OpenNormalSubgroup H, (R : Subgroup H) ≤ (N : Subgroup H) ∧
      (∀ n m : (N : Subgroup H), Commute
        (QuotientGroup.mk' (R : Subgroup H) (n : H))
        (QuotientGroup.mk' (R : Subgroup H) (m : H))) ∧
      (∀ h : H, (∀ n : (N : Subgroup H), Commute
        (QuotientGroup.mk' (R : Subgroup H) h)
        (QuotientGroup.mk' (R : Subgroup H) (n : H))) → h ∈ N) := by
  have : CompactSpace (N : Subgroup H) :=
    N.toOpenSubgroup.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  have : TotallyDisconnectedSpace (TopologicalAbelianization (N : Subgroup H)) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator (N : Subgroup H))
      (Subgroup.isClosed_closedCommutator (N : Subgroup H))
  obtain ⟨U, hU⟩ := exists_faithful_invariantOpenNormalQuotientAction
    (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))
    (continuous_quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) hfaithful
  exact ⟨invariantAbelianQuotientKernel N U, invariantAbelianQuotientKernel_le N U,
    invariantAbelianQuotientKernel_commute N U,
    mem_of_invariantAbelianQuotientKernel_centralizes N U hU⟩

/-- The canonical finite embedding problem arising from the ambient kernel. -/
noncomputable def invariantAbelianEmbeddingProblem [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    TopologicalEmbeddingProblem H where
  A := TopGrp.of (H ⧸ (invariantAbelianQuotientKernel N U : Subgroup H))
  B := TopGrp.of (H ⧸ (N : Subgroup H))
  α := ProC.OpenNormalSubgroup.transition
    (invariantAbelianQuotientKernel_le N U)
  surjective_α := ProC.OpenNormalSubgroup.transition_surjective
    (invariantAbelianQuotientKernel_le N U)
  φ := ProC.OpenNormalSubgroup.quotientProj N
  surjective_φ := ProC.OpenNormalSubgroup.quotientProj_surjective N

/-- The ambient quotient projection is a proper solution. -/
noncomputable def invariantAbelianEmbeddingProblemProperSolution [CompactSpace H]
    (N : OpenNormalSubgroup H)
    (U : OpenNormalSubgroup (TopologicalAbelianization (N : Subgroup H))) :
    (invariantAbelianEmbeddingProblem N U).ProperSolution :=
  ⟨ProC.OpenNormalSubgroup.quotientProj (invariantAbelianQuotientKernel N U),
    ProC.OpenNormalSubgroup.quotientProj_surjective (invariantAbelianQuotientKernel N U),
    ProC.OpenNormalSubgroup.transition_comp_quotientProj
      (invariantAbelianQuotientKernel_le N U)⟩

/-- A continuous homomorphism with commutative image identifies any two elements
identified by topological abelianization. -/
theorem map_eq_of_topologicalAbelianization_eq
    {D : Type u} [Group D] [TopologicalSpace D] [T1Space D]
    (f : H →ₜ* D) (hcomm : ∀ x y : H, Commute (f x) (f y))
    {x y : H}
    (hxy : TopologicalAbelianization.mk H x = TopologicalAbelianization.mk H y) :
    f x = f y := by
  let : CommGroup f.toMonoidHom.range :=
    { (inferInstance : Group f.toMonoidHom.range) with
      mul_comm := by
        intro a b
        obtain ⟨x, hx⟩ := a.property
        obtain ⟨y, hy⟩ := b.property
        apply Subtype.ext
        change (a : D) * (b : D) = (b : D) * (a : D)
        rw [← hx, ← hy]
        exact (hcomm x y).eq }
  let fr : H →ₜ* f.toMonoidHom.range :=
    { toMonoidHom := f.toMonoidHom.rangeRestrict
      continuous_toFun := f.continuous_toFun.subtype_mk
        (fun x => ⟨x, rfl⟩) }
  have hr : fr x = fr y := by
    calc
      fr x = TopologicalAbelianization.lift fr (TopologicalAbelianization.mk H x) :=
        (TopologicalAbelianization.lift_apply_mk fr x).symm
      _ = TopologicalAbelianization.lift fr (TopologicalAbelianization.mk H y) :=
        congrArg (TopologicalAbelianization.lift fr) hxy
      _ = fr y := TopologicalAbelianization.lift_apply_mk fr y
  exact congrArg Subtype.val hr

/-- An abelian image of `N` with no larger centralizer detects every nontrivial
element of the conjugation action on the topological abelianization of `N`. -/
theorem injective_quotientConjugation_of_selfCentralizing_image
    {D : Type u} [Group D] [TopologicalSpace D] [T1Space D]
    (N : OpenNormalSubgroup H) (θ : H →ₜ* D)
    (hcomm : ∀ n m : (N : Subgroup H), Commute
      (θ (n : H)) (θ (m : H)))
    (hcentralizer : ∀ h : H, (∀ n : (N : Subgroup H), Commute
      (θ h) (θ (n : H))) → h ∈ N) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H)) := by
  apply (injective_iff_map_eq_one
    (quotientConjugationTopologicalAbelianizationMap (N : Subgroup H))).mpr
  intro q hq
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (N : Subgroup H) q
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup H)) h).mpr
  apply hcentralizer h
  intro n
  let f : (N : Subgroup H) →ₜ* D :=
    { toMonoidHom := θ.toMonoidHom.comp (N : Subgroup H).subtype
      continuous_toFun := θ.continuous_toFun.comp continuous_subtype_val }
  have hab : TopologicalAbelianization.mk (N : Subgroup H) (MulAut.conjNormal h n) =
      TopologicalAbelianization.mk (N : Subgroup H) n := by
    rw [← quotientConjugationTopologicalAbelianizationMap_mk_apply_mk, hq, MulAut.one_apply]
  have hf : f (MulAut.conjNormal h n) = f n :=
    map_eq_of_topologicalAbelianization_eq f hcomm hab
  change θ (h * (n : H) * h⁻¹) = θ (n : H) at hf
  rw [map_mul, map_mul, map_inv] at hf
  exact (mul_inv_eq_iff_eq_mul).mp hf

/-- Abelianization-faithfulness is equivalent to the existence of finite ambient
quotients in which each open normal subgroup has abelian, self-centralizing image. -/
theorem isAbFaithful_iff_exists_abelian_selfCentralizing_quotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    IsAbFaithful G ↔
      ∀ H : OpenSubgroup G, ∀ N : OpenNormalSubgroup (H : Subgroup G),
        ∃ R : OpenNormalSubgroup (H : Subgroup G),
          (R : Subgroup (H : Subgroup G)) ≤ (N : Subgroup (H : Subgroup G)) ∧
          (∀ n m : (N : Subgroup (H : Subgroup G)), Commute
            (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) (n : (H : Subgroup G)))
            (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) (m : (H : Subgroup G)))) ∧
          (∀ h : (H : Subgroup G), (∀ n : (N : Subgroup (H : Subgroup G)), Commute
            (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) h)
            (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) (n : (H : Subgroup G)))) →
              h ∈ N) := by
  constructor
  · intro hG H N
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    exact exists_openNormal_abelian_selfCentralizing_quotient N (hG H N)
  · intro hG H N
    obtain ⟨R, hRN, hcomm, hcentralizer⟩ := hG H N
    exact injective_quotientConjugation_of_selfCentralizing_image N
      (ProC.OpenNormalSubgroup.quotientProj R) hcomm hcentralizer

/-- Every finite quotient of every open subgroup admits a proper finite embedding
problem with abelian kernel and faithful conjugation action of the given target. -/
def HasFiniteFaithfulAbelianEmbeddingSolutions
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ H : OpenSubgroup G, ∀ B : TopGrp.{u},
    Finite B → DiscreteTopology B →
      ∀ π : (H : Subgroup G) →ₜ* B, ∀ hπ : Function.Surjective π,
        ∃ E : TopGrp.{u}, Finite E ∧ DiscreteTopology E ∧
          ∃ α : E →ₜ* B, ∃ hα : Function.Surjective α,
            ∃ hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E),
              Function.Injective (abelianKernelConjugation α.toMonoidHom hα hcomm) ∧
                Nonempty (⟨E, B, α, hα, π, hπ⟩ :
                  TopologicalEmbeddingProblem (H : Subgroup G)).ProperSolution

/-- The finite faithful abelian embedding formulation of abelianization-faithfulness. -/
theorem isAbFaithful_iff_hasFiniteFaithfulAbelianEmbeddingSolutions
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    IsAbFaithful G ↔ HasFiniteFaithfulAbelianEmbeddingSolutions G := by
  constructor
  · intro hG H B hBfinite hBdiscrete π hπ
    have : DiscreteTopology B := hBdiscrete
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    let N : OpenNormalSubgroup (H : Subgroup G) := ProC.OpenNormalSubgroup.ker π
    obtain ⟨R, hRN, hcommR, hcentralizerR⟩ :=
      exists_openNormal_abelian_selfCentralizing_quotient N (hG H N)
    let E : TopGrp.{u} := TopGrp.of ((H : Subgroup G) ⧸ (R : Subgroup (H : Subgroup G)))
    let α : E →ₜ* B := QuotientGroup.liftₜ (R : Subgroup (H : Subgroup G)) π hRN
    have hαmk (h : (H : Subgroup G)) :
        α (QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) h) = π h := rfl
    have hα : Function.Surjective α := by
      intro b
      obtain ⟨h, rfl⟩ := hπ b
      exact ⟨QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) h, hαmk h⟩
    have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E) := by
      intro a b
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) (a : E)
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) (b : E)
      have hxN : x ∈ N := by
        change π x = 1
        rw [← hαmk, hx]
        exact a.property
      have hyN : y ∈ N := by
        change π y = 1
        rw [← hαmk, hy]
        exact b.property
      rw [← hx, ← hy]
      exact hcommR ⟨x, hxN⟩ ⟨y, hyN⟩
    have hfaithful : Function.Injective (abelianKernelConjugation α.toMonoidHom hα hcomm) := by
      apply (abelianKernelConjugation_injective_iff α.toMonoidHom hα hcomm).mpr
      intro e he
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (R : Subgroup (H : Subgroup G)) e
      change π h = 1
      apply hcentralizerR h
      intro n
      apply he ⟨QuotientGroup.mk' (R : Subgroup (H : Subgroup G)) (n : (H : Subgroup G)), ?_⟩
      change π (n : (H : Subgroup G)) = 1
      exact n.property
    refine ⟨E, inferInstance, inferInstance, α, hα, hcomm, hfaithful, ?_⟩
    exact ⟨⟨ProC.OpenNormalSubgroup.quotientProj R,
      ProC.OpenNormalSubgroup.quotientProj_surjective R, rfl⟩⟩
  · intro hG H N
    let B : TopGrp.{u} := TopGrp.of ((H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G)))
    have : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    obtain ⟨E, hEfinite, hEdiscrete, α, hα, hcomm, hfaithful, ⟨θ⟩⟩ :=
      hG H B inferInstance inferInstance (ProC.OpenNormalSubgroup.quotientProj N)
        (ProC.OpenNormalSubgroup.quotientProj_surjective N)
    have : DiscreteTopology E := hEdiscrete
    have hsquare (h : (H : Subgroup G)) :
        α (θ.val h) = ProC.OpenNormalSubgroup.quotientProj N h :=
      DFunLike.congr_fun θ.property.2 h
    have hθN (n : (N : Subgroup (H : Subgroup G))) : θ.val (n : (H : Subgroup G)) ∈
        α.toMonoidHom.ker := by
      change α (θ.val (n : (H : Subgroup G))) = 1
      rw [hsquare]
      exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mpr n.property
    apply injective_quotientConjugation_of_selfCentralizing_image N θ.val
    · intro n m
      exact hcomm ⟨θ.val (n : (H : Subgroup G)), hθN n⟩
        ⟨θ.val (m : (H : Subgroup G)), hθN m⟩
    · intro h hh
      have hker : θ.val h ∈ α.toMonoidHom.ker := by
        apply (abelianKernelConjugation_injective_iff α.toMonoidHom hα hcomm).mp hfaithful
        intro a
        obtain ⟨n, hn⟩ := θ.property.1 (a : E)
        have hnN : n ∈ N := by
          apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
          rw [← hsquare, hn]
          exact a.property
        rw [← hn]
        exact hh ⟨n, hnN⟩
      apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
      rw [← hsquare]
      exact hker

end ProCGroups.FiniteStepSolvableQuotients
