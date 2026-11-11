/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Nyll.ProCGroups.FreeProC.Basic
public import Nyll.ProCGroups.Generation.Basic
public import Nyll.ProCGroups.Profinite.OpenSubgroups

/-!
# Universe-polymorphic targets for free pro-\(C\) groups

The original IsFreeProCGroup API keeps the source, free group, finite-group class, and target in
one universe. This module factors the universal property for one fixed target into
HasFreeLiftTo and provides extension operations from a witness for an independent target
universe. Cross-universe membership is expressed by FiniteGroupClass.MemAcrossUniverses, so no
ULift appears in the public universal property.

The ordinary universal property supplies the independent-target witness. Finite quotients lift
through native in-class representatives; generation enforces their compatibility, and the
canonical profinite inverse limit gives the required continuous homomorphism.
-/

@[expose] public section

open Set CategoryTheory
open scoped Topology

namespace ProCGroups.FreeProC

universe u v

open ProCGroups

variable {C : FiniteGroupClass.{u}}

/-- The universal extension property from F to one fixed pro-\(C\) target G.

Keeping this target-specific property separate lets constructions state exactly the
cross-universe lifting witness they supply. The ordinary free universal property constructs
this witness for every independent target universe below. -/
def HasFreeLiftTo
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ProC.HasOpenNormalBasisInClassAcrossUniverses C G →
    ∀ (φ : X → G), Continuous φ →
      ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

namespace HasFreeLiftTo

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Extend a continuous generator map to the fixed target. -/
noncomputable def lift (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →* G :=
  Classical.choose (ExistsUnique.exists (h hG φ hφ))

/-- The fixed-target lift is continuous and has the prescribed generator values. -/
theorem lift_spec (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) :
    Continuous (h.lift hG φ hφ) ∧ ∀ x, h.lift hG φ hφ (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (h hG φ hφ))

/-- The fixed-target lift is unique among continuous homomorphisms with the prescribed values. -/
theorem lift_unique (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = h.lift hG φ hφ :=
  (h hG φ hφ).unique ⟨hf, hfac⟩ (h.lift_spec hG φ hφ)

/-- Bundle the fixed-target lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := h.lift hG φ hφ
  continuous_toFun := (h.lift_spec hG φ hφ).1

end HasFreeLiftTo

/-- The free pro-\(C\) universal property for targets in an explicitly independent universe.

Lean cannot quantify over universe levels inside a proposition, so the target universe v is a
universe parameter of this structure. The native universal property is retained as a parent, so
this stronger witness is directly usable anywhere an IsFreeProCGroup is expected. -/
structure IsFreeProCGroupForTargetUniverse
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop extends IsFreeProCGroup (C := C) ι where
  /--
  For every pro-`C` target in universe `v`, continuous maps from `X` extend uniquely to
  continuous homomorphisms from `F`.
  -/
  hasFreeLiftTo :
    ∀ {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
      HasFreeLiftTo (C := C) ι G

namespace IsFreeProCGroupForTargetUniverse

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- Extend a continuous generator map to a homomorphism into a target in the chosen target
universe. -/
noncomputable def lift (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →* G :=
  (hι.hasFreeLiftTo (G := G)).lift hG φ hφ

/-- The cross-universe lift is continuous and has the prescribed generator values. -/
theorem lift_spec (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) :
    Continuous (hι.lift hG φ hφ) ∧
      ∀ x, hι.lift hG φ hφ (ι x) = φ x :=
  (hι.hasFreeLiftTo (G := G)).lift_spec hG φ hφ

/-- The cross-universe lift is unique among continuous homomorphisms with the prescribed values. -/
theorem lift_unique (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ := by
  exact (hι.hasFreeLiftTo (G := G)).lift_unique hG φ hφ hf hfac

/-- Bundle the cross-universe lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ
  continuous_toFun := (hι.lift_spec hG φ hφ).1

end IsFreeProCGroupForTargetUniverse

namespace IsFreeProCGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- Continuous homomorphisms into any Hausdorff group agree when they agree on the generators. -/
theorem continuousHom_ext (hι : IsFreeProCGroup (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]
    {f g : F →ₜ* G} (hfg : ∀ x, f (ι x) = g (ι x)) : f = g := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  exact hfg x

/-- The native universal property extends to targets in an independent universe.

Each finite quotient receives a lift through an in-class refinement represented in the native
universe. Generation makes these actual lifts compatible, and the canonical profinite limit
recovers the target without an extra lifting hypothesis or a choice of comparison maps. -/
theorem hasFreeLiftTo (hι : IsFreeProCGroup (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    HasFreeLiftTo (C := C) ι G := by
  classical
  intro hG φ hφ
  let P : ProfiniteGrp.{v} := ProfiniteGrp.of G
  let D := ProfiniteGrp.diagram P
  let π (U : OpenNormalSubgroup G) : G →ₜ* D.obj U :=
    ((ProfiniteGrp.limitCone D).π.app U).hom.comp (ProfiniteGrp.toLimit P).hom
  have hstage (U : OpenNormalSubgroup G) :
      ∃ f : F →ₜ* D.obj U, ∀ x, f (ι x) = π U (φ x) := by
    obtain ⟨V, hVU, H, hH, ⟨e⟩⟩ :=
      hG (U : Set G) U.toOpenSubgroup.isOpen' U.one_mem
    let : TopologicalSpace H := ⊥
    let : DiscreteTopology H := ⟨rfl⟩
    let : Finite (D.obj V) := openNormalSubgroup_finiteQuotient (G := G) V
    let : DiscreteTopology (D.obj V) := Finite.instDiscreteTopology
    let e' : H ≃ₜ* D.obj V :=
      { e with
        continuous_toFun := continuous_of_discreteTopology
        continuous_invFun := continuous_of_discreteTopology }
    have hHC : ProC.HasOpenNormalBasisInClass C H := by
      intro W _hW h1W
      let B : OpenNormalSubgroup H :=
        { toOpenSubgroup :=
            { toSubgroup := ⊥
              isOpen' := isOpen_discrete _ } }
      refine ⟨B, ?_, C.mem_of_mulEquiv QuotientGroup.quotientBot.symm hH⟩
      intro x hx
      change x = 1 at hx
      exact hx.symm ▸ h1W
    let ψ : X → H := fun x => e'.symm (π V (φ x))
    have hψ : Continuous ψ :=
      e'.symm.continuous_toFun.comp ((π V).continuous_toFun.comp hφ)
    let fV : F →ₜ* H := hι.liftHom hHC ψ hψ
    let q : D.obj V →ₜ* D.obj U :=
      (D.map (CategoryTheory.homOfLE (show V ≤ U from hVU))).hom
    let f : F →ₜ* D.obj U :=
      q.comp ((ContinuousMonoidHom.toContinuousMonoidHom e').comp fV)
    refine ⟨f, ?_⟩
    intro x
    change q (e' (hι.lift hHC ψ hψ (ι x))) = π U (φ x)
    rw [(hι.lift_spec hHC ψ hψ).2 x]
    change q (e' (e'.symm (π V (φ x)))) = π U (φ x)
    rw [e'.apply_symm_apply]
    rfl
  let f (U : OpenNormalSubgroup G) : F →ₜ* D.obj U := Classical.choose (hstage U)
  have hf (U : OpenNormalSubgroup G) (x : X) : f U (ι x) = π U (φ x) :=
    Classical.choose_spec (hstage U) x
  have hcompat {U V : OpenNormalSubgroup G} (i : U ⟶ V) :
      (D.map i).hom.comp (f U) = f V := by
    apply hι.continuousHom_ext
    intro x
    change D.map i (f U (ι x)) = f V (ι x)
    rw [hf U x, hf V x]
    rfl
  let fL : F →ₜ* ProfiniteGrp.limit D :=
    { toFun := fun y => ⟨fun U => f U y, by
        intro U V i
        exact congrArg (fun g : F →ₜ* D.obj V => g y) (hcompat i)⟩
      map_one' := Subtype.ext (funext fun U => (f U).map_one)
      map_mul' := fun x y => Subtype.ext (funext fun U => (f U).map_mul x y)
      continuous_toFun := continuous_induced_rng.mpr (continuous_pi fun U =>
        (f U).continuous_toFun) }
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  let lift : F →ₜ* G := (ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp fL
  have hlift (x : X) : lift (ι x) = φ x := by
    apply e.injective
    change e (e.symm (fL (ι x))) = e (φ x)
    rw [e.apply_symm_apply]
    apply ProfiniteGrp.limit_ext
    intro U
    exact hf U x
  refine ⟨lift.toMonoidHom, ⟨lift.continuous_toFun, hlift⟩, ?_⟩
  intro g hg
  have h : (⟨g, hg.1⟩ : F →ₜ* G) = lift :=
    hι.continuousHom_ext (fun x => (hg.2 x).trans (hlift x).symm)
  exact congrArg ContinuousMonoidHom.toMonoidHom h

/-- The ordinary free pro-C property supplies the independent target-universe property. -/
theorem toForTargetUniverse (hι : IsFreeProCGroup (C := C) ι) :
    IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι where
  toIsFreeProCGroup := hι
  hasFreeLiftTo := hι.hasFreeLiftTo

end IsFreeProCGroup

end ProCGroups.FreeProC
