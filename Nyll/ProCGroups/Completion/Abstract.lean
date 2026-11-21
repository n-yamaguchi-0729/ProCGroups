/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Nyll.ProCGroups.Completion.Topological

/-!
# Comparison with the abstract profinite completion

The abstract completion is Mathlib's completion of the underlying group.
Its canonical map is algebraic. The open-quotient construction on a discrete
copy supplies a comparison model and retains the existing universal property
for profinite targets in an independent universe.

When every finite-index normal subgroup is open in the given topology, the
open-quotient completion and the abstract completion are canonically
isomorphic as topological groups.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace LocalClassFieldTheory

universe u v

/-- A copy of a group equipped with the discrete topology. -/
@[ext]
structure AbstractProfiniteSource (G : Type u) where
  /-- The underlying group element. -/
  val : G

namespace AbstractProfiniteSource

variable (G : Type u)

/-- The tautological equivalence between the discrete copy and the underlying type. -/
def equiv : AbstractProfiniteSource G ≃ G where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The discrete source copy inherits the group structure of `G`. -/
instance [Group G] : Group (AbstractProfiniteSource G) := (equiv G).group

/-- The abstract profinite source carries the discrete topology. -/
instance : TopologicalSpace (AbstractProfiniteSource G) := ⊥

/-- The topology on the abstract profinite source is discrete. -/
instance : DiscreteTopology (AbstractProfiniteSource G) := ⟨rfl⟩

/-- The discrete source copy of a group is a topological group. -/
instance [Group G] : IsTopologicalGroup (AbstractProfiniteSource G) := inferInstance

/-- The tautological multiplicative equivalence from the discrete copy. -/
def mulEquiv [Group G] : AbstractProfiniteSource G ≃* G where
  toEquiv := equiv G
  map_mul' _ _ := rfl

end AbstractProfiniteSource

/-- The abstract profinite completion is Mathlib's completion of the original group. -/
noncomputable def AbstractProfiniteCompletion
    (G : Type u) [Group G] : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)

/-- The canonical algebraic map into the abstract profinite completion. -/
noncomputable def abstractProfiniteCompletionMapMonoidHom
    (G : Type u) [Group G] : G →* AbstractProfiniteCompletion G :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom

/-- The same canonical map is continuous on the discrete source copy. -/
noncomputable def abstractProfiniteCompletionClass
    (G : Type u) [Group G] :
    AbstractProfiniteSource G →ₜ* AbstractProfiniteCompletion G where
  toMonoidHom := (abstractProfiniteCompletionMapMonoidHom G).comp
    (AbstractProfiniteSource.mulEquiv G).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The open-quotient model's canonical map on the original underlying group. -/
noncomputable def abstractProfiniteCompletionModelMapMonoidHom
    (G : Type u) [Group G] :
    G →* TopologicalProfiniteCompletion (AbstractProfiniteSource G) :=
  (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)).toMonoidHom.comp
    (AbstractProfiniteSource.mulEquiv G).symm.toMonoidHom

/-- Mathlib's abstract completion agrees with the discrete open-quotient model.
Both directions extend the same canonical maps, so their composites are the
identity by density. -/
noncomputable def abstractProfiniteCompletionEquivModel
    (G : Type u) [Group G] :
    AbstractProfiniteCompletion G ≃ₜ*
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) := by
  let f : AbstractProfiniteCompletion G →ₜ*
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) :=
    (ProfiniteGrp.ProfiniteCompletion.lift
      (P := TopologicalProfiniteCompletion (AbstractProfiniteSource G))
      (GrpCat.ofHom (abstractProfiniteCompletionModelMapMonoidHom G))).hom
  let g : TopologicalProfiniteCompletion (AbstractProfiniteSource G) →ₜ*
      AbstractProfiniteCompletion G :=
    topologicalProfiniteCompletionLift (AbstractProfiniteCompletion G)
      (abstractProfiniteCompletionClass G)
  have hf (x : G) : f (abstractProfiniteCompletionMapMonoidHom G x) =
      abstractProfiniteCompletionModelMapMonoidHom G x := by
    exact CategoryTheory.ConcreteCategory.congr_hom
      (ProfiniteGrp.ProfiniteCompletion.lift_eta
        (P := TopologicalProfiniteCompletion (AbstractProfiniteSource G))
        (GrpCat.ofHom (abstractProfiniteCompletionModelMapMonoidHom G))) x
  have hg (x : AbstractProfiniteSource G) :
      g (topologicalProfiniteCompletionMap (AbstractProfiniteSource G) x) =
        abstractProfiniteCompletionClass G x :=
    topologicalProfiniteCompletionLift_map (AbstractProfiniteCompletion G)
      (abstractProfiniteCompletionClass G) x
  have hgf : Function.LeftInverse g f := by
    intro x
    have h : (fun y => g (f y)) = (fun y => y) :=
      (ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of G)).equalizer
        (g.continuous.comp f.continuous) continuous_id <| by
          funext y
          change g (f (abstractProfiniteCompletionMapMonoidHom G y)) =
            abstractProfiniteCompletionMapMonoidHom G y
          rw [hf]
          change g (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)
            ((AbstractProfiniteSource.mulEquiv G).symm y)) =
              abstractProfiniteCompletionMapMonoidHom G y
          rw [hg]
          rfl
    exact congrFun h x
  have hfg : Function.RightInverse g f := by
    intro x
    have h : (fun y => f (g y)) = (fun y => y) :=
      (topologicalProfiniteCompletionMap_denseRange (AbstractProfiniteSource G)).equalizer
        (f.continuous.comp g.continuous) continuous_id <| by
          funext y
          change f (g (topologicalProfiniteCompletionMap (AbstractProfiniteSource G) y)) =
            topologicalProfiniteCompletionMap (AbstractProfiniteSource G) y
          rw [hg]
          change f (abstractProfiniteCompletionMapMonoidHom G y.val) = _
          rw [hf]
          rfl
    exact congrFun h x
  let e : AbstractProfiniteCompletion G ≃*
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg
      map_mul' := f.map_mul }
  exact ⟨e, f.continuous, g.continuous⟩

/-- The comparison sends a canonical abstract class to the same model class. -/
@[simp] theorem abstractProfiniteCompletionEquivModel_class
    (G : Type u) [Group G] (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g) =
      topologicalProfiniteCompletionMap (AbstractProfiniteSource G) g := by
  exact CategoryTheory.ConcreteCategory.congr_hom
    (ProfiniteGrp.ProfiniteCompletion.lift_eta
      (P := TopologicalProfiniteCompletion (AbstractProfiniteSource G))
      (GrpCat.ofHom (abstractProfiniteCompletionModelMapMonoidHom G))) g.val

/-- The class map has dense image because it is Mathlib's canonical map on
an equivalent underlying source. -/
theorem abstractProfiniteCompletionClass_denseRange
    (G : Type u) [Group G] :
    DenseRange (abstractProfiniteCompletionClass G) := by
  have hrange : Set.range (abstractProfiniteCompletionClass G) =
      Set.range (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G)) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.val, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g⟩, rfl⟩
  change Dense (Set.range (abstractProfiniteCompletionClass G))
  rw [hrange]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of G)

/-- Extend a continuous homomorphism from the discrete source across the
stable abstract profinite completion.  This is the representation-independent
universal-property entry point for `AbstractProfiniteCompletion`. -/
noncomputable def abstractProfiniteCompletionLift
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    AbstractProfiniteCompletion G →ₜ* P :=
  (topologicalProfiniteCompletionLift P f).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (abstractProfiniteCompletionEquivModel G))

/-- The universal lift agrees with the original map on abstract completion classes. -/
@[simp] theorem abstractProfiniteCompletionLift_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P)
    (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionLift G P f
        (abstractProfiniteCompletionClass G g) = f g := by
  unfold abstractProfiniteCompletionLift
  change topologicalProfiniteCompletionLift P f
      (abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g)) = f g
  rw [abstractProfiniteCompletionEquivModel_class,
    topologicalProfiniteCompletionLift_map]

/-- Composing the universal lift with the class map recovers the source homomorphism. -/
@[simp] theorem abstractProfiniteCompletionLift_comp_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    (abstractProfiniteCompletionLift G P f).comp
        (abstractProfiniteCompletionClass G) = f := by
  ext g
  exact abstractProfiniteCompletionLift_class G P f g

/-- A continuous homomorphism out of the stable abstract completion is
determined by its values on the canonical dense class map. -/
theorem abstractProfiniteCompletionLift_unique
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P)
    (h : AbstractProfiniteCompletion G →ₜ* P)
    (hh : h.comp (abstractProfiniteCompletionClass G) = f) :
    h = abstractProfiniteCompletionLift G P f := by
  let e := abstractProfiniteCompletionEquivModel G
  let hModel :
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) →ₜ* P :=
    h.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  have hModel_comp :
      hModel.comp
          (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)) = f := by
    ext g
    change h (e.symm
      (topologicalProfiniteCompletionMap (AbstractProfiniteSource G) g)) = f g
    have hclass : e.symm
        (topologicalProfiniteCompletionMap (AbstractProfiniteSource G) g) =
          abstractProfiniteCompletionClass G g := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (abstractProfiniteCompletionEquivModel_class G g).symm
    rw [hclass]
    exact DFunLike.congr_fun hh g
  have hModel_eq :=
    topologicalProfiniteCompletionLift_unique P f hModel hModel_comp
  apply ContinuousMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hModel_eq (e x)
  change h (e.symm (e x)) =
    topologicalProfiniteCompletionLift P f (e x) at hx
  rw [e.symm_apply_apply] at hx
  change h x = topologicalProfiniteCompletionLift P f (e x)
  exact hx

section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The completion map sends `g` to the class of its discrete source copy. -/
@[simp] theorem abstractProfiniteCompletionMapMonoidHom_apply (g : G) :
    abstractProfiniteCompletionMapMonoidHom G g =
      abstractProfiniteCompletionClass G
        ((AbstractProfiniteSource.mulEquiv G).symm g) :=
  rfl

/-- If every finite-index normal subgroup is open, the abstract completion map
is continuous for the original topology. -/
private theorem abstractProfiniteCompletionModelMapMonoidHom_continuous
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    Continuous (abstractProfiniteCompletionModelMapMonoidHom G) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro H
  let e : G ≃* AbstractProfiniteSource G :=
    (AbstractProfiniteSource.mulEquiv G).symm
  let K : Subgroup G := H.toOpenNormalSubgroup.toSubgroup.comap e.toMonoidHom
  have hKnormal : K.Normal :=
    H.toOpenNormalSubgroup.toSubgroup.normal_comap e.toMonoidHom
  have hKfinite : K.FiniteIndex := by
    constructor
    rw [H.toOpenNormalSubgroup.toSubgroup.index_comap_of_surjective e.surjective]
    exact H.finiteIndex'.index_ne_zero
  have hKopen : IsOpen (K : Set G) := hOpen K hKnormal hKfinite
  apply Continuous.mk
  intro s _
  change IsOpen
    ((fun g : G =>
      (QuotientGroup.mk (e g) :
        AbstractProfiniteSource G ⧸ H.toOpenNormalSubgroup.toSubgroup)) ⁻¹' s)
  let q : G → AbstractProfiniteSource G ⧸ H.toOpenNormalSubgroup.toSubgroup :=
    fun g => QuotientGroup.mk (e g)
  change IsOpen (q ⁻¹' s)
  rw [← Set.biUnion_preimage_singleton q s]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  let representative : G := e.symm (Quotient.out i)
  convert IsOpen.leftCoset hKopen representative using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  simp only [representative, Set.mem_smul_set_iff_inv_smul_mem]
  change (Quotient.out i)⁻¹ * e x ∈ H.toOpenNormalSubgroup.toSubgroup ↔
    representative⁻¹ * x ∈ K
  simp only [OpenSubgroup.mem_toSubgroup, MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_comap,
    MonoidHom.coe_ofClass, map_mul, map_inv, MulEquiv.apply_symm_apply, K, representative]

/-- If every finite-index normal subgroup is open, the abstract completion map
is continuous for the original topology. -/
theorem abstractProfiniteCompletionMapMonoidHom_continuous
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    Continuous (abstractProfiniteCompletionMapMonoidHom G) := by
  let e := abstractProfiniteCompletionEquivModel G
  apply (e.symm.continuous_toFun.comp
    (abstractProfiniteCompletionModelMapMonoidHom_continuous G hOpen)).congr
  intro g
  apply e.injective
  change e (e.symm (abstractProfiniteCompletionModelMapMonoidHom G g)) =
    e (abstractProfiniteCompletionMapMonoidHom G g)
  exact (e.apply_symm_apply _).trans (abstractProfiniteCompletionEquivModel_class G
    ((AbstractProfiniteSource.mulEquiv G).symm g)).symm

/-- The canonical continuous map from the topological completion to the
abstract completion. -/
def topologicalProfiniteCompletionToAbstract
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    TopologicalProfiniteCompletion G →ₜ* AbstractProfiniteCompletion G :=
  topologicalProfiniteCompletionLift
    (AbstractProfiniteCompletion G)
    { toMonoidHom := abstractProfiniteCompletionMapMonoidHom G
      continuous_toFun := abstractProfiniteCompletionMapMonoidHom_continuous G hOpen }

/-- The comparison map agrees with the abstract completion map on the source group. -/
theorem topologicalProfiniteCompletionToAbstract_map
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G))
    (g : G) :
    topologicalProfiniteCompletionToAbstract G hOpen
        (topologicalProfiniteCompletionMap G g) =
      abstractProfiniteCompletionClass G
        ((AbstractProfiniteSource.mulEquiv G).symm g) := by
  unfold topologicalProfiniteCompletionToAbstract
  rw [topologicalProfiniteCompletionLift_map]
  exact abstractProfiniteCompletionMapMonoidHom_apply G g

/-- The canonical continuous map from the abstract completion to the
topological completion. -/
def abstractProfiniteCompletionToTopological :
    AbstractProfiniteCompletion G →ₜ* TopologicalProfiniteCompletion G :=
  abstractProfiniteCompletionLift G
    (TopologicalProfiniteCompletion G)
    { toMonoidHom :=
        (topologicalProfiniteCompletionMap G).toMonoidHom.comp
          (AbstractProfiniteSource.mulEquiv G).toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }

/-- The reverse comparison map agrees with the topological completion map on the discrete source. -/
theorem abstractProfiniteCompletionToTopological_map
    (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionToTopological G
        (abstractProfiniteCompletionClass G g) =
      topologicalProfiniteCompletionMap G (AbstractProfiniteSource.mulEquiv G g) := by
  unfold abstractProfiniteCompletionToTopological
  rw [abstractProfiniteCompletionLift_class]
  rfl

/-- Under the condition that all finite-index normal subgroups are open, the
open-quotient completion is canonically the abstract profinite completion. -/
def topologicalProfiniteCompletion_compare_abstract
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    TopologicalProfiniteCompletion G ≃ₜ* AbstractProfiniteCompletion G := by
  let forward := topologicalProfiniteCompletionToAbstract G hOpen
  let backward := abstractProfiniteCompletionToTopological G
  have hleft : backward.comp forward = ContinuousMonoidHom.id _ := by
    calc
      backward.comp forward =
          topologicalProfiniteCompletionLift
            (TopologicalProfiniteCompletion G)
            (topologicalProfiniteCompletionMap G) := by
        apply topologicalProfiniteCompletionLift_unique
        ext g
        simp only [ContinuousMonoidHom.comp_toFun, topologicalProfiniteCompletionToAbstract_map,
          abstractProfiniteCompletionToTopological_map, MulEquiv.apply_symm_apply, backward,
          forward]
      _ = ContinuousMonoidHom.id _ := by
        symm
        apply topologicalProfiniteCompletionLift_unique
        rfl
  have hright : forward.comp backward = ContinuousMonoidHom.id _ := by
    calc
      forward.comp backward =
          abstractProfiniteCompletionLift G
            (AbstractProfiniteCompletion G)
            (abstractProfiniteCompletionClass G) := by
        apply abstractProfiniteCompletionLift_unique
        ext g
        simp only [ContinuousMonoidHom.comp_toFun, abstractProfiniteCompletionToTopological_map,
          topologicalProfiniteCompletionToAbstract_map, MulEquiv.symm_apply_apply, forward,
          backward]
      _ = ContinuousMonoidHom.id _ := by
        symm
        apply abstractProfiniteCompletionLift_unique
        rfl
  let e : TopologicalProfiniteCompletion G ≃* AbstractProfiniteCompletion G :=
    { toFun := forward
      invFun := backward
      left_inv := fun x => by
        have hx := congrArg (fun f => f x) hleft
        exact hx
      right_inv := fun y => by
        have hy := congrArg (fun f => f y) hright
        exact hy
      map_mul' := forward.map_mul }
  exact ContinuousMulEquiv.mk e forward.continuous_toFun backward.continuous_toFun

end Comparison

end LocalClassFieldTheory
