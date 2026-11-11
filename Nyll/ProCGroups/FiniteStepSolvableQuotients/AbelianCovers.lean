/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Solvable quotients of abelian covers

An open subgroup of the `(n + 1)`-step quotient whose preimage contains the
closed commutator determines the actual `n`-step quotient of that preimage.
In particular, three-step input retains the metabelian quotient of an abelian
cover. The comparison is continuous and is induced by the original projection.
This is the group-theoretic comparison; existence and descent of curve covers
remain separate geometric tasks.
-/

@[expose] public section

namespace ProCGroups.FiniteStepSolvableQuotients

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ambient `(n + 1)`-step kernel lies in the preimage cover's `n`th
closed derived subgroup. This supplies the kernel bound, rather than assuming it. -/
theorem abelianCover_restrictPreimage_ker_le
    (n : ℕ) (H : OpenSubgroup (MaxSolvQuot G (n + 1)))
    (hfirst : topDerivedTop G 1 ≤
      (H : Subgroup (MaxSolvQuot G (n + 1))).comap
        (toMaxSolvQuot G (n + 1))) :
    (ContinuousMonoidHom.restrictPreimage (continuousToMaxSolvQuot G (n + 1))
      (H : Subgroup (MaxSolvQuot G (n + 1)))).ker ≤
      topDerivedTop ((H : Subgroup (MaxSolvQuot G (n + 1))).comap
        (toMaxSolvQuot G (n + 1))) n := by
  let Hpre := preimageOpenSubgroup (continuousToMaxSolvQuot G (n + 1)) H
  have hbound : topDerivedTop G (n + 1) ≤
      (topDerivedTop (Hpre : Subgroup G) n).map (Hpre : Subgroup G).subtype := by
    simpa only [Nat.add_sub_cancel] using
      topDerivedTop_le_openSubgroup_pred_map_of_first_le Hpre
        (Nat.le_add_left 1 n) hfirst
  intro x hx
  have hxker : continuousToMaxSolvQuot G (n + 1) x.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  obtain ⟨y, hy, hyx⟩ := hbound (continuousToMaxSolvQuot_eq_one_iff.mp hxker)
  exact (Subtype.ext hyx : y = x) ▸ hy

variable [CompactSpace G]

/-- The canonical continuous comparison of the solvable quotients of an
abelian cover before and after taking the ambient solvable quotient. -/
noncomputable def abelianCoverSolvableQuotientEquiv
    (n : ℕ) (H : OpenSubgroup (MaxSolvQuot G (n + 1)))
    (hfirst : topDerivedTop G 1 ≤
      (H : Subgroup (MaxSolvQuot G (n + 1))).comap
        (toMaxSolvQuot G (n + 1))) :
    MaxSolvQuot ((H : Subgroup (MaxSolvQuot G (n + 1))).comap
      (toMaxSolvQuot G (n + 1))) n ≃ₜ* MaxSolvQuot (H : Subgroup (MaxSolvQuot G (n + 1))) n := by
  let π := continuousToMaxSolvQuot G (n + 1)
  let Hpre := (H : Subgroup (MaxSolvQuot G (n + 1))).comap π.toMonoidHom
  have hHclosed : IsClosed ((H : Subgroup (MaxSolvQuot G (n + 1))) :
      Set (MaxSolvQuot G (n + 1))) := openSubgroup_isClosed H
  have hpreclosed : IsClosed (Hpre : Set G) := hHclosed.preimage π.continuous
  have : CompactSpace Hpre := hpreclosed.isClosedEmbedding_subtypeVal.compactSpace
  let f := ContinuousMonoidHom.restrictPreimage π (H : Subgroup (MaxSolvQuot G (n + 1)))
  have hclosed : IsClosedMap f :=
    _root_.TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap π
      (H : Subgroup (MaxSolvQuot G (n + 1))) π.continuous.isClosedMap hHclosed
  let e := TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv
    (π := π) (Q₁ := (H : Subgroup (MaxSolvQuot G (n + 1)))) (m := n)
    (continuousToMaxSolvQuot_surjective G (n + 1)) hclosed
    (abelianCover_restrictPreimage_ker_le n H hfirst)
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 (topMaxSolvQuotMap f n).toMonoidHom
    (topMaxSolvQuotMap f n).continuous e.bijective

/-- The comparison agrees with the actual ambient projection on representatives. -/
theorem abelianCoverSolvableQuotientEquiv_apply_mk
    (n : ℕ) (H : OpenSubgroup (MaxSolvQuot G (n + 1)))
    (hfirst : topDerivedTop G 1 ≤
      (H : Subgroup (MaxSolvQuot G (n + 1))).comap
        (toMaxSolvQuot G (n + 1)))
    (x : (H : Subgroup (MaxSolvQuot G (n + 1))).comap
      (toMaxSolvQuot G (n + 1))) :
    abelianCoverSolvableQuotientEquiv n H hfirst (toMaxSolvQuot _ n x) =
      toMaxSolvQuot _ n
        (ContinuousMonoidHom.restrictPreimage (continuousToMaxSolvQuot G (n + 1))
          (H : Subgroup (MaxSolvQuot G (n + 1))) x) := rfl

end ProCGroups.FiniteStepSolvableQuotients
