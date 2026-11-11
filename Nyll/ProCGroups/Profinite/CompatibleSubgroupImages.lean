/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Basic

/-!
# Images of compatible subgroups of compact quotient systems

Let a compact group map to a directed family of groups, with each chosen subgroup
contained in the corresponding map range. If the
transition maps carry each chosen closed subgroup onto the earlier chosen
subgroup, then the simultaneous inverse image maps onto every chosen
subgroup. The proof uses closed fibers in the original compact group, rather
than an assumed inverse-limit comparison or a choice of compatible lifts.

The intended application is the actual normalization wild subgroup and its
literal finite inertia restrictions. Neither commutativity nor finiteness of
the quotient groups is needed for the compactness argument.
-/

@[expose] public section

noncomputable section

namespace Subgroup

variable {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    {H : ι → Type*} [∀ i, Group (H i)]

/-- Closed original fibers suffice to recover the exact image of a compatible
subgroup family whose members lie in the respective map ranges. No topology on the
target groups is chosen. -/
theorem map_iInf_comap_of_compact_closedFibers_of_le_range
    (f : ∀ i, G →* H i)
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i))
    (hcover : ∀ i, W i ≤ (f i).range)
    (hclosed : ∀ i, IsClosed (f i ⁻¹' (W i : Set (H i))))
    (hfiber : ∀ i y, IsClosed {g : G | f i g = y})
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  classical
  have hmem (i l : ι) (hil : i ≤ l) (g : G) (hg : f l g ∈ W l) :
      f i g ∈ W i := by
    rw [← hmap i l hil]
    exact ⟨f l g, hg, hcomp i l hil g⟩
  apply le_antisymm
  · rintro y ⟨g, hg, rfl⟩
    exact (Subgroup.mem_iInf.mp hg) j
  · intro y hy
    let C (i : ι) : Set G := {g | f i g ∈ W i ∧ f j g = y}
    have hCclosed (i : ι) : IsClosed (C i) := (hclosed i).inter (hfiber j y)
    have hCnonempty (i : ι) : (C i).Nonempty := by
      have hy' : y ∈ (W (i ⊔ j)).map (r j (i ⊔ j) le_sup_right) := by
        rw [hmap]
        exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      obtain ⟨g, hg⟩ := hcover (i ⊔ j) hz
      have hgw : f (i ⊔ j) g ∈ W (i ⊔ j) := hg.symm ▸ hz
      refine ⟨g, hmem i (i ⊔ j) le_sup_left g hgw, ?_⟩
      rw [← hcomp j (i ⊔ j) le_sup_right g, hg]
      exact hzy
    have hCdirected : Directed (· ⊇ ·) C := by
      intro i l
      refine ⟨i ⊔ l, ?_, ?_⟩
      · intro g hg
        exact ⟨hmem i (i ⊔ l) le_sup_left g hg.1, hg.2⟩
      · intro g hg
        exact ⟨hmem l (i ⊔ l) le_sup_right g hg.1, hg.2⟩
    obtain ⟨g, hg⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        C hCdirected hCnonempty (fun i => (hCclosed i).isCompact) hCclosed
    refine ⟨g, Subgroup.mem_iInf.mpr (fun i => ?_), ?_⟩
    · exact (Set.mem_iInter.mp hg i).1
    · exact (Set.mem_iInter.mp hg j).2

/-- Closed original fibers suffice to recover the exact image of a compatible
subgroup family. No topology on the target groups is chosen. -/
theorem map_iInf_comap_of_compact_closedFibers
    (f : ∀ i, G →* H i) (hsurj : ∀ i, Function.Surjective (f i))
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i))
    (hclosed : ∀ i, IsClosed (f i ⁻¹' (W i : Set (H i))))
    (hfiber : ∀ i y, IsClosed {g : G | f i g = y})
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  exact map_iInf_comap_of_compact_closedFibers_of_le_range f r hcomp W
    (fun i y _ => hsurj i y) hclosed hfiber hmap j

/-- Compatible closed subgroups contained in the original map ranges are the exact
images of their simultaneous inverse image in the original compact group. -/
theorem map_iInf_comap_of_compact_of_le_range
    [∀ i, TopologicalSpace (H i)] [∀ i, T1Space (H i)]
    (f : ∀ i, G →* H i) (hf : ∀ i, Continuous (f i))
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i)) (hcover : ∀ i, W i ≤ (f i).range)
    (hclosed : ∀ i, IsClosed (W i : Set (H i)))
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  apply map_iInf_comap_of_compact_closedFibers_of_le_range f r hcomp W hcover
  · exact fun i => (hclosed i).preimage (hf i)
  · exact fun i y =>
      (isClosed_singleton : IsClosed ({y} : Set (H i))).preimage (hf i)
  · exact hmap

/-- Compatible closed subgroups with surjective transitions are the exact
images of their simultaneous inverse image in the original compact group. -/
theorem map_iInf_comap_of_compact_surjective
    [∀ i, TopologicalSpace (H i)] [∀ i, T1Space (H i)]
    (f : ∀ i, G →* H i) (hf : ∀ i, Continuous (f i))
    (hsurj : ∀ i, Function.Surjective (f i))
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i)) (hclosed : ∀ i, IsClosed (W i : Set (H i)))
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  exact map_iInf_comap_of_compact_of_le_range f hf r hcomp W
    (fun i y _ => hsurj i y) hclosed hmap j

/-- For locally constant original restrictions covering the chosen subgroups, no target topology
and no separate closedness assertion are needed. This applies directly to the
intrinsic finite normalization groups with their original group laws. -/
theorem map_iInf_comap_of_locallyConstant_of_le_range
    (f : ∀ i, G →* H i) (hf : ∀ i, IsLocallyConstant (f i))
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i)) (hcover : ∀ i, W i ≤ (f i).range)
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  apply map_iInf_comap_of_compact_closedFibers_of_le_range f r hcomp W hcover
  · exact fun i => ⟨hf i (W i : Set (H i))ᶜ⟩
  · exact fun i y => ⟨hf i ({y} : Set (H i))ᶜ⟩
  · exact hmap

/-- For locally constant original restrictions, no target topology and no
separate closedness assertion are needed. This applies directly to the
intrinsic finite normalization groups with their original group laws. -/
theorem map_iInf_comap_of_locallyConstant
    (f : ∀ i, G →* H i) (hf : ∀ i, IsLocallyConstant (f i))
    (hsurj : ∀ i, Function.Surjective (f i))
    (r : ∀ i j, i ≤ j → H j →* H i)
    (hcomp : ∀ i j (hij : i ≤ j) g, r i j hij (f j g) = f i g)
    (W : ∀ i, Subgroup (H i))
    (hmap : ∀ i j (hij : i ≤ j), (W j).map (r i j hij) = W i)
    (j : ι) :
    (⨅ i, (W i).comap (f i)).map (f j) = W j := by
  exact map_iInf_comap_of_locallyConstant_of_le_range f hf r hcomp W
    (fun i y _ => hsurj i y) hmap j

end Subgroup
