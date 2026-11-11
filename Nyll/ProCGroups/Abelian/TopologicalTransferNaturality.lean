/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalTransferComparison
public import Mathlib.Topology.Maps.Basic

/-!
# Original topological transfer through a quotient

A continuous quotient sends an actual open normal subgroup containing
its kernel to an actual open normal subgroup of the target. The original
subgroup map is surjective, and its kernel is the restricted original
kernel.

The original topological transfer commutes with these quotient maps.
The proof computes on actual representatives and uses the proved
naturality of ordinary group transfer; no Artin map or reconstructed
transition occurs in the construction.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian
open Topology

universe u v

variable {G : Type u} {Q : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- The actual image of an open normal subgroup containing the kernel
of a quotient homomorphism, with its original quotient topology. -/
def openNormalQuotientImage (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup) :
    OpenNormalSubgroup Q where
  toOpenSubgroup :=
    { toSubgroup := N.toSubgroup.map f.toMonoidHom
      isOpen' := by
        apply hf.isCoinducing.isOpen_preimage.mp
        change IsOpen
          (((N.toSubgroup.map f.toMonoidHom).comap f.toMonoidHom) : Set G)
        rw [Subgroup.comap_map_eq_self hker]
        exact N.isOpen' }
  isNormal' := N.isNormal'.map f.toMonoidHom hf.surjective

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The original image subgroup has exactly the original subgroup as
its inverse image because the original kernel is contained in it. -/
theorem openNormalQuotientImage_comap
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup) :
    (openNormalQuotientImage f hf N hker).toSubgroup.comap f.toMonoidHom =
      N.toSubgroup :=
  Subgroup.comap_map_eq_self hker

/-- The actual homomorphism from the original open subgroup to its image. -/
def openNormalQuotientSubgroupMap
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup) :
    N.toSubgroup →ₜ* (openNormalQuotientImage f hf N hker).toSubgroup where
  toMonoidHom := f.toMonoidHom.subgroupMap N.toSubgroup
  continuous_toFun := (f.continuous_toFun.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- On every original subgroup element, this is the actual ambient quotient. -/
theorem openNormalQuotientSubgroupMap_val
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup)
    (x : N.toSubgroup) :
    (openNormalQuotientSubgroupMap f hf N hker x).val = f x.val := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The actual map onto the image open subgroup is surjective. -/
theorem openNormalQuotientSubgroupMap_surjective
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup) :
    Function.Surjective (openNormalQuotientSubgroupMap f hf N hker) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := x.property
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- Its kernel is the literal restriction of the original ambient kernel. -/
theorem openNormalQuotientSubgroupMap_ker
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup) :
    (openNormalQuotientSubgroupMap f hf N hker).toMonoidHom.ker =
      f.toMonoidHom.ker.subgroupOf N.toSubgroup := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The quotient by the actual image subgroup is finite whenever the
original coset space is finite. -/
theorem finite_openNormalQuotientImage
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup)
    [Finite (G ⧸ N.toSubgroup)] :
    Finite (Q ⧸ (openNormalQuotientImage f hf N hker).toSubgroup) := by
  have hNindex : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have himageIndex : (N.toSubgroup.map f.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective
      (H := N.toSubgroup) (f := f.toMonoidHom) hf.surjective
  change Finite (Q ⧸ N.toSubgroup.map f.toMonoidHom)
  infer_instance

/-- Original topological transfer commutes with an actual quotient which
does not change the finite coset space. Both subgroup arrows are the
literal maps induced by the original continuous homomorphism. -/
theorem openNormalTransfer_quotient_natural
    (f : G →ₜ* Q) (hf : IsQuotientMap f)
    (N : OpenNormalSubgroup G) (hker : f.toMonoidHom.ker ≤ N.toSubgroup)
    [Finite (G ⧸ N.toSubgroup)] :
    have _ : Finite (Q ⧸ (openNormalQuotientImage f hf N hker).toSubgroup) :=
      finite_openNormalQuotientImage f hf N hker
    ∀ z : TopologicalAbelianization G,
      TopologicalAbelianization.map (openNormalQuotientSubgroupMap f hf N hker)
          (openNormalTransferTopologicalAbelianization N z) =
        openNormalTransferTopologicalAbelianization
          (openNormalQuotientImage f hf N hker) (TopologicalAbelianization.map f z) := by
  intro hQfinite z
  have hNindex : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have himageIndex : (N.toSubgroup.map f.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective
      (H := N.toSubgroup) (f := f.toMonoidHom) hf.surjective
  obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk G z
  change TopologicalAbelianization.lift
      ((TopologicalAbelianization.mkₜ
        (openNormalQuotientImage f hf N hker).toSubgroup).comp
          (openNormalQuotientSubgroupMap f hf N hker))
      (openNormalTransferTopologicalAbelianization N (TopologicalAbelianization.mk G g)) =
    openNormalTransferTopologicalAbelianization
      (openNormalQuotientImage f hf N hker) (TopologicalAbelianization.mk Q (f g))
  rw [lift_openNormalTransfer_apply_mk]
  change MonoidHom.transfer
      ((TopologicalAbelianization.mk (N.toSubgroup.map f.toMonoidHom)).comp
        (f.toMonoidHom.subgroupMap N.toSubgroup)) g =
    openNormalTransferTopologicalAbelianizationPre
      (openNormalQuotientImage f hf N hker) (f g)
  rw [openNormalTransferPre_eq_transfer]
  exact ClassFormation.transfer_character_natural_of_surjective
    f.toMonoidHom hf.surjective N.toSubgroup hker
    (TopologicalAbelianization.mk (N.toSubgroup.map f.toMonoidHom)) g

end ProCGroups.FiniteStepSolvableQuotients
