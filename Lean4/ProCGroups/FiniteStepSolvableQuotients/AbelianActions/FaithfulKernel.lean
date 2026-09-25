/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Faithful conjugation on an abelian kernel

Conjugation descends along an epimorphism with abelian kernel. Its faithfulness
is characterized by the kernel being its own centralizer.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

universe u v

variable {E : Type u} [Group E] {B : Type v} [Group B]

/-- An abelian kernel acts trivially on itself by conjugation. -/
theorem abelianKernel_le_ker_conjNormal (α : E →* B)
    (hcomm : ∀ a b : α.ker, Commute (a : E) (b : E)) :
    α.ker ≤ (MulAut.conjNormal : E →* MulAut α.ker).ker := by
  intro e he
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change e * (a : E) * e⁻¹ = (a : E)
  rw [(hcomm ⟨e, he⟩ a).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- The action of the quotient target on the abelian kernel of an epimorphism. -/
noncomputable def abelianKernelConjugation (α : E →* B)
    (hsurj : Function.Surjective α)
    (hcomm : ∀ a b : α.ker, Commute (a : E) (b : E)) :
    B →* MulAut α.ker :=
  (QuotientGroup.lift α.ker MulAut.conjNormal
    (abelianKernel_le_ker_conjNormal α hcomm)).comp
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm.toMonoidHom

/-- The descended action agrees with conjugation by every lift. -/
theorem abelianKernelConjugation_apply (α : E →* B)
    (hsurj : Function.Surjective α)
    (hcomm : ∀ a b : α.ker, Commute (a : E) (b : E))
    (e : E) (a : α.ker) :
    abelianKernelConjugation α hsurj hcomm (α e) a = MulAut.conjNormal e a := by
  have hclass :
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α e) =
        QuotientGroup.mk' α.ker e := by
    apply (QuotientGroup.quotientKerEquivOfSurjective α hsurj).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change QuotientGroup.lift α.ker MulAut.conjNormal
    (abelianKernel_le_ker_conjNormal α hcomm)
    ((QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α e)) a = _
  rw [hclass]
  rfl

/-- Faithfulness is equivalent to the abelian kernel being self-centralizing. -/
theorem abelianKernelConjugation_injective_iff (α : E →* B)
    (hsurj : Function.Surjective α)
    (hcomm : ∀ a b : α.ker, Commute (a : E) (b : E)) :
    Function.Injective (abelianKernelConjugation α hsurj hcomm) ↔
      ∀ e : E, (∀ a : α.ker, Commute e (a : E)) → e ∈ α.ker := by
  constructor
  · intro hinj e he
    change α e = 1
    apply hinj
    rw [map_one]
    apply MulEquiv.ext
    intro a
    rw [abelianKernelConjugation_apply]
    apply Subtype.ext
    change e * (a : E) * e⁻¹ = (a : E)
    rw [(he a).eq, mul_assoc, mul_inv_cancel, mul_one]
  · intro hcentralizer
    apply (injective_iff_map_eq_one (abelianKernelConjugation α hsurj hcomm)).mpr
    intro b hb
    obtain ⟨e, rfl⟩ := hsurj b
    apply hcentralizer e
    intro a
    have ha := congrArg (fun σ : MulAut α.ker => (σ a : E)) hb
    rw [abelianKernelConjugation_apply] at ha
    change e * (a : E) * e⁻¹ = (a : E) at ha
    exact (mul_inv_eq_iff_eq_mul).mp ha

end ProCGroups.FiniteStepSolvableQuotients
