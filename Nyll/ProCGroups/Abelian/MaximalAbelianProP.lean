/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# The actual maximal abelian pro-p quotient

We first take the full topological abelianization, then its existing maximal
pro-p residual quotient. The projection, its kernel, the universal property,
and functorial maps are constructed from those two actual quotients.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian

open ProC

universe u

/-- The maximal pro-p quotient of the full topological abelianization. -/
abbrev AbelianProPQuotient (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  TopologicalAbelianization G ⧸
    proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization G)

namespace AbelianProPQuotient

variable (p : ℕ) [Fact p.Prime]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical continuous projection to the maximal abelian pro-p quotient. -/
def mk : G →ₜ* AbelianProPQuotient p G :=
  { toMonoidHom :=
      (QuotientGroup.mk'
        (proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization G))).comp
          (TopologicalAbelianization.mk G)
    continuous_toFun := QuotientGroup.continuous_mk.comp
      (TopologicalAbelianization.mkₜ G).continuous_toFun }

/-- Both quotient projections are surjective. -/
theorem surjective_mk : Function.Surjective (mk p G) :=
  (QuotientGroup.mk'_surjective _).comp (TopologicalAbelianization.surjective_mk G)

/-- The closed kernel of the canonical projection. -/
def kernel : Subgroup G := (mk p G).toMonoidHom.ker

instance kernel_normal : (kernel p G).Normal :=
  MonoidHom.normal_ker (mk p G).toMonoidHom

instance instT2Space : T2Space (AbelianProPQuotient p G) := by
  have : IsClosed
      (proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization G) :
        Set (TopologicalAbelianization G)) := proCResidualCore_isClosed _ _
  infer_instance

/-- Closedness is inherited from the kernel of a continuous map to a Hausdorff group. -/
theorem kernel_isClosed : IsClosed (kernel p G : Set G) :=
  ContinuousMonoidHom.isClosed_ker (mk p G)

/-- A kernel element is exactly an element whose canonical class is one. -/
@[simp] theorem mem_kernel {x : G} : x ∈ kernel p G ↔ mk p G x = 1 := Iff.rfl

variable {G}

/-- Maps out of the maximal abelian pro-p quotient are determined on representatives. -/
@[ext] theorem hom_ext
    {A : Type u} [Group A] [TopologicalSpace A]
    {f g : AbelianProPQuotient p G →ₜ* A}
    (h : ∀ x : G, f (mk p G x) = g (mk p G x)) : f = g := by
  ext q
  obtain ⟨x, rfl⟩ := surjective_mk p G q
  exact h x

variable [CompactSpace G]

/-- Every continuous homomorphism to a Hausdorff abelian pro-p group descends. -/
noncomputable def lift
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (f : G →ₜ* A) (hA : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A) :
    AbelianProPQuotient p G →ₜ* A :=
  lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary p)
    (TopologicalAbelianization.lift f) hA

/-- The descended map applies the original map to representatives. -/
@[simp] theorem lift_apply_mk
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (f : G →ₜ* A) (hA : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A)
    (x : G) : lift p f hA (mk p G x) = f x := rfl

/-- The actual kernel is killed by every continuous map to a Hausdorff abelian pro-p group. -/
theorem kernel_le_ker
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (f : G →ₜ* A) (hA : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A) :
    kernel p G ≤ f.toMonoidHom.ker := by
  intro x hx
  change f x = 1
  rw [← lift_apply_mk p f hA x, (mem_kernel p G).mp hx, map_one]

/-- The universal property as an actual equivalence of continuous Hom sets. -/
noncomputable def homEquiv
    (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (hA : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A) :
    (AbelianProPQuotient p G →ₜ* A) ≃ (G →ₜ* A) where
  toFun f := f.comp (mk p G)
  invFun f := lift p f hA
  left_inv f := by
    apply hom_ext
    intro x
    rfl
  right_inv f := by
    ext x
    rfl

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism induces the map of the two actual quotient groups. -/
noncomputable def map (f : G →ₜ* H) :
    AbelianProPQuotient p G →ₜ* AbelianProPQuotient p H :=
  QuotientGroup.mapₜ
    (proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization G))
    (proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization H))
    (TopologicalAbelianization.map f)
    (Subgroup.map_le_iff_le_comap.mp
      (map_proCResidualCore_le_of_continuousMonoidHom
        (FiniteGroupClass.pGroup_hereditary p) (TopologicalAbelianization.map f)))

/-- Functoriality on the original group representatives. -/
@[simp] theorem map_apply_mk (f : G →ₜ* H) (x : G) :
    map p f (mk p G x) = mk p H (f x) := rfl

/-- Continuous homomorphisms preserve the actual abelian pro-p kernels. -/
theorem map_kernel_le (f : G →ₜ* H) :
    (kernel p G).map f.toMonoidHom ≤ kernel p H := by
  rintro y ⟨x, hx, rfl⟩
  change mk p H (f x) = 1
  rw [← map_apply_mk, (mem_kernel p G).mp hx, map_one]

/-- The induced map of the identity is the identity. -/
@[simp] theorem map_id : map p (ContinuousMonoidHom.id G) =
    ContinuousMonoidHom.id (AbelianProPQuotient p G) := by
  apply hom_ext
  intro x
  rfl

/-- The maps of actual abelian pro-p quotients respect composition. -/
@[simp] theorem map_comp [CompactSpace H]
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (g : H →ₜ* K) (f : G →ₜ* H) :
    map p (g.comp f) = (map p g).comp (map p f) := by
  apply hom_ext
  intro x
  rfl

variable (G) [T2Space G] [TotallyDisconnectedSpace G]

instance instTotallyDisconnectedSpace : TotallyDisconnectedSpace (AbelianProPQuotient p G) := by
  have : TotallyDisconnectedSpace (TopologicalAbelianization G) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (proCResidualCore (FiniteGroupClass.pGroup p) (TopologicalAbelianization G))
    (proCResidualCore_isClosed _ _)

/-- For a profinite source, the constructed abelian quotient really is pro-p. -/
theorem hasOpenNormalBasisInClass :
    HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (AbelianProPQuotient p G) := by
  have : TotallyDisconnectedSpace (TopologicalAbelianization G) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  exact proCResidualCoreQuotient_hasOpenNormalBasisInClass (FiniteGroupClass.pGroup_formation p)

end AbelianProPQuotient

end ProCGroups.Abelian
