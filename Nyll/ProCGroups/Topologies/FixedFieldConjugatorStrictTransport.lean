/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport
import Mathlib.FieldTheory.Galois.Basic

/-! # Strict transport after the computed discrepancies fix the same field

The same automorphisms, now proved to fix E, are regarded as E-automorphisms.
An actual target-group lift removes their residual inner discrepancy. Its
change to any equivariant fibre map is the explicit translation supplied by
the imported correction theorem.
-/
noncomputable section

namespace ProCGroups

variable (k E κ : Type*) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]

/-- Regard the same computed automorphism as an E-automorphism once its
pointwise fixing property has been proved. -/
def algEquivOfPointwiseFixing
    (σ : Gal(κ/k)) (hσ : ∀ a : E, σ (algebraMap E κ a) = algebraMap E κ a) : Gal(κ/E) :=
  { σ.toRingEquiv with commutes' := hσ }

@[simp] theorem algEquivOfPointwiseFixing_restrictScalars
    (σ : Gal(κ/k)) (hσ : ∀ a : E, σ (algebraMap E κ a) = algebraMap E κ a) :
    (algEquivOfPointwiseFixing k E κ σ hσ).restrictScalars k = σ := by
  ext x
  rfl

/-- Restriction to k loses no information about the same automorphism of κ. -/
theorem restrictScalars_injective_fixedField :
    Function.Injective (fun σ : Gal(κ/E) => σ.restrictScalars k) := by
  intro σ τ h
  exact AlgEquiv.ext fun x => congrArg (fun a : Gal(κ/k) => a x) h

/-- The residual discrepancy is the quotient of the two computed
E-automorphisms, in the exact order forced by the arithmetic equations. -/
theorem fixedField_quotient_transport_conjugate
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (α : G ≃ₜ* H)
    (qs : G →* Gal(κ/E)) (qt : H →* Gal(κ/E))
    (qsk : G →* Gal(κ/k)) (qtk : H →* Gal(κ/k))
    (cs ct : Gal(κ/E))
    (hα : ∀ g, qtk (α g) = qsk g)
    (hs : ∀ g, (qs g).restrictScalars k =
      cs.restrictScalars k * qsk g * (cs.restrictScalars k)⁻¹)
    (ht : ∀ h, (qt h).restrictScalars k =
      ct.restrictScalars k * qtk h * (ct.restrictScalars k)⁻¹)
    (g : G) :
    qt (α g) = (ct * cs⁻¹) * qs g * (ct * cs⁻¹)⁻¹ := by
  apply restrictScalars_injective_fixedField k E κ
  change (qt (α g)).restrictScalars k =
    (ct.restrictScalars k * (cs.restrictScalars k)⁻¹) *
      (qs g).restrictScalars k *
      (ct.restrictScalars k * (cs.restrictScalars k)⁻¹)⁻¹
  rw [ht, hα, hs]
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

/-- An actual target-group lift produces strict Gal(κ/E) compatibility.
The correction is returned, so its action on the same fibre map and chosen
point remains visible to downstream callers. -/
theorem exists_fixedField_strict_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (α : G ≃ₜ* H)
    (qs : G →* Gal(κ/E)) (qt : H →* Gal(κ/E))
    (qsk : G →* Gal(κ/k)) (qtk : H →* Gal(κ/k))
    (cs ct : Gal(κ/E))
    (hα : ∀ g, qtk (α g) = qsk g)
    (hs : ∀ g, (qs g).restrictScalars k =
      cs.restrictScalars k * qsk g * (cs.restrictScalars k)⁻¹)
    (ht : ∀ h, (qt h).restrictScalars k =
      ct.restrictScalars k * qtk h * (ct.restrictScalars k)⁻¹)
    (hqt : Function.Surjective qt) :
    ∃ c : H, qt c = (ct * cs⁻¹)⁻¹ ∧
      ∀ g, qt (innerCorrectedGroupEquiv α c g) = qs g := by
  exact exists_innerCorrection_strict_quotient α qs qt hqt (ct * cs⁻¹)
    (fixedField_quotient_transport_conjugate k E κ α qs qt qsk qtk cs ct hα hs ht)

end ProCGroups
