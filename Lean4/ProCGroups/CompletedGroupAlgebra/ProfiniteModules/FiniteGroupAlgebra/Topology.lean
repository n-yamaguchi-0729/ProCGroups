import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.Basic.OpenIdeals
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Topology and universal maps for finite group algebras

A finite group algebra over a profinite coefficient ring is identified with a finite product of
coefficients and given its profinite ring topology. This file proves continuity of its operations
and constructs continuous linear lifts from basis data.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w

/--
The product topology on the group algebra of a finite group, transported through \(R[G] = G
\to_0 R \simeq G \to R\). This is the finite stage used in the construction of the completed
group algebra.
-/
@[reducible]
noncomputable def finiteGroupAlgebraTopology
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    TopologicalSpace (MonoidAlgebra R G) :=
  TopologicalSpace.induced
    ((MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans
      Finsupp.equivFunOnFinite : MonoidAlgebra R G ≃ (G → R))
    inferInstance

/--
The finite group algebra with its transported product topology is homeomorphic to the function
space \(G \to R\).
-/
noncomputable def finiteGroupAlgebraHomeomorph
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃ₜ (G → R) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R G → G → R) :=
    Topology.IsInducing.induced e
  exact e.toHomeomorphOfIsInducing he

/--
The finite-stage group algebra is the finite product of copies of the coefficient ring as a
topological \(R\)-module.
-/
noncomputable def finiteGroupAlgebraContinuousLinearEquivPi
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃L[R] (G → R) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R G → G → R) :=
    Topology.IsInducing.induced e
  exact ContinuousLinearEquiv.mk
    ((MonoidAlgebra.coeffLinearEquiv R).trans
      (Finsupp.linearEquivFunOnFinite R R G))
    (by
      change Continuous (e : MonoidAlgebra R G → G → R)
      exact he.continuous)
    (by
      change Continuous ((e.toHomeomorphOfIsInducing he).symm : (G → R) → MonoidAlgebra R G)
      exact (e.toHomeomorphOfIsInducing he).symm.continuous)

/-- The continuous equivalence is evaluated by the corresponding comparison formula. -/
@[simp]
theorem finiteGroupAlgebraContinuousLinearEquivPi_apply
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    (x : MonoidAlgebra R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraContinuousLinearEquivPi R G x =
      Finsupp.equivFunOnFinite x.coeff :=
  rfl

/--
Coordinate evaluation on a finite group algebra is continuous for the transported product
topology.
-/
theorem finiteGroupAlgebra_coordinate_continuous
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ∀ g : G, Continuous fun x : MonoidAlgebra R G => x.coeff g := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  intro g
  change Continuous ((fun p : G → R => p g) ∘
    (e : MonoidAlgebra R G → G → R))
  exact
    (continuous_apply g).comp
      (continuous_induced_dom : Continuous (e : MonoidAlgebra R G → G → R))

/-- Addition is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousAdd
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousAdd (MonoidAlgebra R G) := by
  classical
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x.coeff g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : A × A => p.1.coeff g + p.2.coeff g
  exact ((hcoord g).comp continuous_fst).add ((hcoord g).comp continuous_snd)

/-- Negation is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousNeg
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousNeg (MonoidAlgebra R G) := by
  classical
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x.coeff g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun x : A => -x.coeff g
  exact (hcoord g).neg

/--
Multiplication is continuous for the finite-stage group algebra topology. The coordinate formula
is the finite convolution sum over pairs (g1,g2) with \(g1*g2 = g\).
-/
theorem finiteGroupAlgebra_continuousMul
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousMul (MonoidAlgebra R G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x.coeff g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : A × A => (p.1 * p.2).coeff g
  rw [show (fun p : A × A => (p.1 * p.2).coeff g) =
      (fun p : A × A => ∑ q ∈ (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g)),
        p.1.coeff q.1 * p.2.coeff q.2) from ?_]
  · apply continuous_finsetSum
    intro q _hq
    exact ((hcoord q.1).comp continuous_fst).mul ((hcoord q.2).comp continuous_snd)
  · funext p
    exact MonoidAlgebra.coeff_mul_antidiag p.1 p.2 g
      (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g)) (by intro q; simp only
          [Finset.mem_filter, Finset.mem_univ, true_and])

/--
Scalar multiplication by the coefficient ring is continuous on the finite-stage group algebra
topology.
-/
theorem finiteGroupAlgebra_continuousSMul
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousSMul R (MonoidAlgebra R G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let A := MonoidAlgebra R G
  let e : A ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : A → G → R) := Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : A => x.coeff g :=
    finiteGroupAlgebra_coordinate_continuous R G
  refine ContinuousSMul.mk ?_
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun p : R × A => p.1 * p.2.coeff g
  exact continuous_fst.mul ((hcoord g).comp continuous_snd)

/-- The finite-stage group algebra topology makes \(R[G]\) a topological ring. -/
theorem finiteGroupAlgebra_isTopologicalRing
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsTopologicalRing (MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  letI : ContinuousAdd (MonoidAlgebra R G) := finiteGroupAlgebra_continuousAdd R G
  letI : ContinuousMul (MonoidAlgebra R G) := finiteGroupAlgebra_continuousMul R G
  letI : ContinuousNeg (MonoidAlgebra R G) := finiteGroupAlgebra_continuousNeg R G
  letI : IsTopologicalSemiring (MonoidAlgebra R G) := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- Compactness of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_compactSpace
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [CompactSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    CompactSpace (MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.compactSpace (finiteGroupAlgebraHomeomorph R G).symm

/-- The Hausdorff property of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_t2Space
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [T2Space R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    T2Space (MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.t2Space (finiteGroupAlgebraHomeomorph R G).symm

/-- Total disconnectedness of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_totallyDisconnectedSpace
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [TotallyDisconnectedSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    TotallyDisconnectedSpace (MonoidAlgebra R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.totallyDisconnectedSpace (finiteGroupAlgebraHomeomorph R G).symm

/--
The finite function-space lift sends a coefficient function to the finite sum of its
coefficients acting on the prescribed values.
-/
private noncomputable def finiteGroupAlgebraPiLift
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) : (G -> R) →L[R] N where
  toLinearMap :=
    { toFun := fun m => ∑ x : G, m x • f x
      map_add' := by
        intro m n
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro lam m
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]}
  cont := by
    apply continuous_finsetSum
    intro x _hx
    exact (continuous_apply x).smul continuous_const

/--
The finite function-space lift sends the basis function \(\mathrm{Pi.single}\ g\ 1\) to
\(f(g)\).
-/
private theorem finiteGroupAlgebraPiLift_apply_basis
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G] [DecidableEq G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) (g : G) :
    finiteGroupAlgebraPiLift R G N f (Pi.single g (1 : R)) = f g := by
  simp only [finiteGroupAlgebraPiLift, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/--
A continuous linear map out of a finite group algebra is determined by its values on group
elements.
-/
noncomputable def finiteGroupAlgebraLift
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G →L[R] N := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact
    { toLinearMap :=
        (finiteGroupAlgebraPiLift R G N f).toLinearMap.comp
          ((MonoidAlgebra.coeffLinearEquiv R).trans
            (Finsupp.linearEquivFunOnFinite R R G)).toLinearMap
      cont :=
        by
          have hcont :
              Continuous
                (((MonoidAlgebra.coeffLinearEquiv R).trans
                  (Finsupp.linearEquivFunOnFinite R R G)) :
                  MonoidAlgebra R G → G → R) := by
            let e := finiteGroupAlgebraHomeomorph R G
            change Continuous ((e : MonoidAlgebra R G ≃ₜ (G → R)) :
              MonoidAlgebra R G → G → R)
            exact e.continuous
          exact (finiteGroupAlgebraPiLift R G N f).continuous.comp hcont }

/-- The finite group-algebra lift sends the group-like basis vector at \(g\) to \(f(g)\). -/
@[simp]
theorem finiteGroupAlgebraLift_apply_of
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Group G] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) (g : G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraLift R G N f (MonoidAlgebra.of R G g) = f g := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  rw [show MonoidAlgebra.of R G g =
    (MonoidAlgebra.single g 1 : MonoidAlgebra R G) by rfl]
  change finiteGroupAlgebraPiLift R G N f
      ((Finsupp.linearEquivFunOnFinite R R G)
        ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R G).coeff)) =
    f g
  rw [MonoidAlgebra.coeff_single]
  rw [Finsupp.linearEquivFunOnFinite_single]
  exact finiteGroupAlgebraPiLift_apply_basis R G N f g

end CompletedGroupAlgebra
