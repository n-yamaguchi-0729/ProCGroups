import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Projection

/-!
# Fox differential: in class — system — ring — group like

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraOfInClass`
  The class-restricted completed group-algebra element represented by a group element.
- `primePowerCompletedGroupAlgebraProjectionInClass_of`
  The \(C\)-indexed prime-power completed group-algebra projection sends a group-like element to its
  finite-stage group-like class.
- `primePowerCompletedGroupAlgebraOfInClass_one`
  The canonical map to the class-indexed prime-power completed group algebra sends \(1\) to \(1\).
- `primePowerCompletedGroupAlgebraOfInClass_mul`
  The canonical map to the class-indexed prime-power completed group algebra preserves
  multiplication.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The class-restricted completed group-algebra element represented by a group element. -/
def primePowerCompletedGroupAlgebraOfInClass
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (h : H) :
    PrimePowerCompletedGroupAlgebraInClass ell H C := by
  refine ⟨fun i => ?_, ?_⟩
  · exact
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h)
  · intro i j hij
    change primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ell) (G := H) C hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ j.1))
          (CompletedGroupAlgebraQuotientInClass H C j.2)
          (QuotientGroup.mk h)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h)
    rw [primePowerCompletedGroupAlgebraTransitionInClass_of]
    rfl

/--
The \(C\)-indexed prime-power completed group-algebra projection sends a group-like element to
its finite-stage group-like class.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_of
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass H C)
    (h : H) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
        (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h) := by
  rfl

/--
The canonical map to the class-indexed prime-power completed group algebra sends \(1\) to \(1\).
-/
@[simp]
theorem primePowerCompletedGroupAlgebraOfInClass_one
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) :
    primePowerCompletedGroupAlgebraOfInClass (ell := ell) (H := H) C 1 = 1 := by
  apply Subtype.ext
  funext i
  change primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) (H := H) C 1) =
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (1 : PrimePowerCompletedGroupAlgebraInClass ell H C)
  rw [primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_one]
  exact map_one
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (CompletedGroupAlgebraQuotientInClass H C i.2))

/--
The canonical map to the class-indexed prime-power completed group algebra preserves
multiplication.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraOfInClass_mul
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (C : ProCGroups.FiniteGroupClass.{u}) (h₁ h₂ : H) :
    primePowerCompletedGroupAlgebraOfInClass (ell := ell) C (h₁ * h₂) =
      primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₁ *
        primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₂ := by
  apply Subtype.ext
  funext i
  change primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C (h₁ * h₂)) =
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ell) (G := H) C i
      (primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₁ *
        primePowerCompletedGroupAlgebraOfInClass (ell := ell) C h₂)
  rw [primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_mul,
    primePowerCompletedGroupAlgebraProjectionInClass_of,
    primePowerCompletedGroupAlgebraProjectionInClass_of]
  change
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (CompletedGroupAlgebraQuotientInClass H C i.2))
        (QuotientGroup.mk (h₁ * h₂)) =
      (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (CompletedGroupAlgebraQuotientInClass H C i.2))
          (QuotientGroup.mk h₁) *
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
          (CompletedGroupAlgebraQuotientInClass H C i.2))
            (QuotientGroup.mk h₂)
  rw [QuotientGroup.mk_mul]
  exact map_mul
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (CompletedGroupAlgebraQuotientInClass H C i.2))
    (QuotientGroup.mk h₁) (QuotientGroup.mk h₂)

end

end FoxDifferential
