import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.Projection

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — coeff — system

The principal declarations in this module are:

- `primePowerCompletedCoeffSystem`
  The coefficient inverse system over prime-power group-algebra indices; at index \((a, U)\), its
  coefficient ring is \(\mathbb{Z}/\ell^a\mathbb{Z}\).
- `PrimePowerCompletedCoeff`
  The inverse-limit object of the coefficient tower indexed by prime powers and quotients.
- `primePowerCompletedCoeffProjection`
  The projection from the prime-power coefficient limit to one finite stage.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The coefficient inverse system over prime-power group-algebra indices; at index \((a, U)\), its
coefficient ring is \(\mathbb{Z}/\ell^a\mathbb{Z}\).
-/
def primePowerCompletedCoeffSystem :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndex G) where
  X := fun i => ZMod (ℓ ^ i.1)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    modNCompletedCoeffMap (n := ℓ ^ i.1) (m := ℓ ^ j.1)
      (primePow_dvd_primePow (ℓ := ℓ) hij.1)
  continuous_map := by
    intro i j hij
    letI : TopologicalSpace (ZMod (ℓ ^ i.1)) := ⊥
    letI : TopologicalSpace (ZMod (ℓ ^ j.1)) := ⊥
    letI : DiscreteTopology (ZMod (ℓ ^ j.1)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_rfl (n := ℓ ^ i.1))) x
  map_comp := by
    intro i j k hij hjk
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    letI : Fact (0 < ℓ ^ k.1) := ⟨primePower_pos ℓ k.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_comp
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) x

/-- The inverse-limit object of the coefficient tower indexed by prime powers and quotients. -/
abbrev PrimePowerCompletedCoeff :=
  (primePowerCompletedCoeffSystem ℓ G).inverseLimit

/-- The projection from the prime-power coefficient limit to one finite stage. -/
abbrev primePowerCompletedCoeffProjection (i : PrimePowerCompletedGroupAlgebraIndex G) :
    PrimePowerCompletedCoeff ℓ G →
      ModNCompletedCoeff (ℓ ^ i.1) :=
  (primePowerCompletedCoeffSystem ℓ G).projection i

end

end FoxDifferential
