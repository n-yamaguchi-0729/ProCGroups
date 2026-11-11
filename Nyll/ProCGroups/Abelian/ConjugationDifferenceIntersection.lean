/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Recovering closed subgroups from all Frobenius displacement quotients

Conjugation in the original profinite ambient group supplies finite
quotients on which a positive power of every specified element is trivial.
Consequently the images of conjugation minus identity become arbitrarily
small. Intersecting the sums with a fixed closed subgroup recovers that
subgroup itself. No prime component or wild part is discarded.
-/

@[expose] public section

noncomputable section

open scoped IsMulCommutative

namespace ProCGroups.Abelian

universe u

/-- Subgroup images commute with conjugation through the same ambient
homomorphism. This is the common calculation for actual stabilizer maps. -/
theorem subgroup_map_conj_comm
    {P Q : Type*} [Group P] [Group Q] (D : Subgroup P) (f : P →* Q) (g : P) :
    (D.map (MulAut.conj g).toMonoidHom).map f =
      (D.map f).map (MulAut.conj (f g)).toMonoidHom := by
  have h : f.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (f g)).toMonoidHom.comp f := by
    ext x
    change f (g * x * g⁻¹) = f g * f x * (f g)⁻¹
    simp only [map_mul, map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, h]

variable {P : Type u} [Group P]
    (A : Subgroup P) [A.Normal] [IsMulCommutative A]

/-- The displacement under conjugation by the specified original ambient
element, on the actual normal commutative subgroup. -/
def conjugationDifference (d : P) : A →* A :=
  { toFun := fun a => MulAut.conjNormal d a / a
    map_one' := by rw [map_one, div_one]
    map_mul' := by
      intro a b
      rw [map_mul]
      exact (div_mul_div_comm _ _ _ _).symm }

/-- The displacement subgroup inside the original ambient group. -/
def conjugationDifferenceImage (d : P) : Subgroup P :=
  (A.subtype.comp (conjugationDifference A d)).range

/-- A positive-power displacement is already an original displacement.
The telescoping identity is computed in the same geometric subgroup. -/
theorem conjugationDifferenceImage_pow_le (d : P) (n : ℕ) :
    conjugationDifferenceImage A (d ^ n) ≤ conjugationDifferenceImage A d := by
  rintro _ ⟨a, rfl⟩
  have h (m : ℕ) : conjugationDifference A (d ^ m) a ∈
      (conjugationDifference A d).range := by
    induction m with
    | zero =>
      change MulAut.conjNormal (d ^ 0) a / a ∈ _
      rw [pow_zero, map_one, MulAut.one_apply, div_self']
      exact (conjugationDifference A d).range.one_mem
    | succ m ih =>
      have hfirst : conjugationDifference A d (MulAut.conjNormal (d ^ m) a) ∈
          (conjugationDifference A d).range := ⟨MulAut.conjNormal (d ^ m) a, rfl⟩
      have hprod := (conjugationDifference A d).range.mul_mem hfirst ih
      change (MulAut.conjNormal d (MulAut.conjNormal (d ^ m) a) /
        MulAut.conjNormal (d ^ m) a) * (MulAut.conjNormal (d ^ m) a / a) ∈ _ at hprod
      rw [div_mul_div_cancel] at hprod
      change MulAut.conjNormal (d ^ (m + 1)) a / a ∈ _
      rw [pow_succ', map_mul, MulAut.mul_apply]
      exact hprod
  obtain ⟨b, hb⟩ := h n
  exact ⟨b, congrArg Subtype.val hb⟩

/-- Once the original conjugating element lies in a normal subgroup,
all its geometric displacements lie in that same subgroup. -/
theorem conjugationDifferenceImage_le_of_mem
    (N : Subgroup P) [N.Normal] (d : P) (hd : d ∈ N) :
    conjugationDifferenceImage A d ≤ N := by
  rintro x ⟨a, rfl⟩
  let q : P →* P ⧸ N := QuotientGroup.mk' N
  have hdq : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
  apply (QuotientGroup.eq_one_iff _).mp
  change q (d * (a : P) * d⁻¹ / (a : P)) = 1
  rw [div_eq_mul_inv]
  simp only [map_mul, map_inv, hdq, one_mul, inv_one, mul_one, mul_inv_cancel]

/-- An ambient homomorphism that is onto the specified geometric subgroup
carries the full displacement image onto the transported displacement image.
Surjectivity on the whole arithmetic group is unnecessary. -/
theorem conjugationDifferenceImage_map_of_hom
    {Q : Type*} [Group Q] (B : Subgroup Q) [B.Normal] [IsMulCommutative B]
    (f : P →* Q) (hAB : A.map f = B) (d : P) :
    (conjugationDifferenceImage A d).map f =
      conjugationDifferenceImage B (f d) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
    have hb : f (a : P) ∈ B := by
      rw [← hAB]
      exact ⟨a, a.property, rfl⟩
    refine ⟨⟨f (a : P), hb⟩, ?_⟩
    change f d * f (a : P) * (f d)⁻¹ / f (a : P) =
      f (d * (a : P) * d⁻¹ / (a : P))
    simp only [map_mul, map_inv, map_div]
  · rintro _ ⟨b, rfl⟩
    have hb : (b : Q) ∈ A.map f := hAB.symm ▸ b.property
    obtain ⟨a, ha, hab⟩ := hb
    refine ⟨d * a * d⁻¹ / a, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    change f (d * a * d⁻¹ / a) = f d * (b : Q) * (f d)⁻¹ / (b : Q)
    simp only [map_mul, map_inv, map_div, hab]

/-- The displacement image is carried by the original ambient isomorphism
to the displacement image for its actual transported conjugating element. -/
theorem conjugationDifferenceImage_map
    {Q : Type*} [Group Q] (B : Subgroup Q) [B.Normal] [IsMulCommutative B]
    (e : P ≃* Q) (hAB : A.map e.toMonoidHom = B) (d : P) :
    (conjugationDifferenceImage A d).map e.toMonoidHom =
      conjugationDifferenceImage B (e d) :=
  conjugationDifferenceImage_map_of_hom A B e.toMonoidHom hAB d

variable [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P]

/-- An actual closed subgroup is recovered from its images modulo all
positive-power conjugation displacements. The finite quotients are those
of the original ambient profinite group, so continuity of a separately
chosen abstract Frobenius action is not an implicit assumption. -/
theorem closedSubgroup_eq_iInf_sup_conjugationDifferenceImage
    (I : Subgroup P) (hI : IsClosed (I : Set P)) (d : P) :
    I = ⨅ n : ℕ+, I ⊔ conjugationDifferenceImage A (d ^ (n : ℕ)) := by
  apply le_antisymm
  · exact le_iInf fun _ => le_sup_left
  · have hsep : I = sInf {N : Subgroup P | IsOpen (N : Set P) ∧ I ≤ N} :=
      ProC.closedSubgroup_eq_sInf_open ⟨I, hI⟩
    refine le_trans ?_ hsep.symm.le
    apply le_sInf
    intro U hU
    obtain ⟨V, hVU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := P) hU.1 U.one_mem
    obtain ⟨n, hn, hdn⟩ := exists_pos_pow_mem_openSubgroup V.toOpenSubgroup d
    have hdiff : conjugationDifferenceImage A (d ^ n) ≤ (V : Subgroup P) :=
      conjugationDifferenceImage_le_of_mem A (V : Subgroup P) (d ^ n) hdn
    have hle : I ⊔ conjugationDifferenceImage A (d ^ n) ≤ U :=
      sup_le hU.2 (hdiff.trans hVU)
    exact (iInf_le (fun m : ℕ+ => I ⊔ conjugationDifferenceImage A (d ^ (m : ℕ)))
      ⟨n, hn⟩).trans hle

/-- Equality at every positive-power displacement quotient forces equality
of the original closed subgroups, including their full wild parts. -/
theorem closedSubgroup_eq_of_sup_conjugationDifferenceImage_eq
    (I J : Subgroup P) (hI : IsClosed (I : Set P)) (hJ : IsClosed (J : Set P))
    (d : P)
    (h : ∀ n : ℕ+, I ⊔ conjugationDifferenceImage A (d ^ (n : ℕ)) =
      J ⊔ conjugationDifferenceImage A (d ^ (n : ℕ))) : I = J := by
  calc
    I = ⨅ n : ℕ+, I ⊔ conjugationDifferenceImage A (d ^ (n : ℕ)) :=
      closedSubgroup_eq_iInf_sup_conjugationDifferenceImage A I hI d
    _ = ⨅ n : ℕ+, J ⊔ conjugationDifferenceImage A (d ^ (n : ℕ)) := iInf_congr h
    _ = J := (closedSubgroup_eq_iInf_sup_conjugationDifferenceImage A J hJ d).symm

omit [IsTopologicalGroup P] [TotallyDisconnectedSpace P] in
/-- Matching the actual displacement quotients at every positive power
under one continuous ambient isomorphism matches the original full closed
subgroups under that same isomorphism. -/
theorem map_closedSubgroup_eq_of_sup_conjugationDifferenceImage_eq
    {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] [T2Space Q]
    (B : Subgroup Q) [B.Normal] [IsMulCommutative B]
    (e : P ≃ₜ* Q) (hAB : A.map e.toMonoidHom = B)
    (I : Subgroup P) (J : Subgroup Q)
    (hI : IsClosed (I : Set P)) (hJ : IsClosed (J : Set Q)) (d : P)
    (h : ∀ n : ℕ+,
      (I ⊔ conjugationDifferenceImage A (d ^ (n : ℕ))).map e.toMonoidHom =
        J ⊔ conjugationDifferenceImage B ((e d) ^ (n : ℕ))) :
    I.map e.toMonoidHom = J := by
  have hImageClosed : IsClosed ((I.map e.toMonoidHom : Subgroup Q) : Set Q) := by
    change IsClosed (e '' (I : Set P))
    exact (hI.isCompact.image e.continuous).isClosed
  apply closedSubgroup_eq_of_sup_conjugationDifferenceImage_eq B
    (I.map e.toMonoidHom) J hImageClosed hJ (e d)
  intro n
  have hn := h n
  rw [Subgroup.map_sup, conjugationDifferenceImage_map A B e.toMulEquiv hAB,
    map_pow] at hn
  exact hn

end ProCGroups.Abelian
