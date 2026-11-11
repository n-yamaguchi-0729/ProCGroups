/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.ConjugationDifferenceIntersection
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.Generation.Basic
public import Mathlib.Tactic.Group

/-!
# The original geometric kernel inside arithmetic abelianization

For a split extension with compact commutative kernel and a specified
topological generator of the arithmetic quotient, the kernel of geometric
restriction to the actual topological abelianization is the image of
conjugation minus identity. A continuous retraction to the corresponding
geometric quotient is constructed from the original splitting. No abstract
cohomology identification or equality of section germs is assumed.
-/

@[expose] public section

noncomputable section

open scoped IsMulCommutative

namespace ProCGroups.Abelian

open Generation

universe u v

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    {Γ : Type v} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (π : P →ₜ* Γ) [IsMulCommutative π.toMonoidHom.ker]
    [CompactSpace π.toMonoidHom.ker]

/-- The actual arithmetic abelianization kills exactly the geometric
displacements under the original lift of an arithmetic topological
generator. The quotient retraction and all continuity are constructed. -/
theorem abelianization_restrict_kernel_eq_conjugationDifference_range
    (s : Γ →ₜ* P) (hs : ∀ g, π (s g) = g)
    (γ : Γ) (hγ : TopologicallyGenerates ({γ} : Set Γ)) :
    ((TopologicalAbelianization.mk P).comp π.toMonoidHom.ker.subtype).ker =
      (conjugationDifference π.toMonoidHom.ker (s γ)).range := by
  let A := π.toMonoidHom.ker
  let N := (conjugationDifference A (s γ)).range
  let T : Γ →* MulAut A :=
    (MulAut.conjNormal : P →* MulAut A).comp s.toMonoidHom
  have hconj (d : P) : Continuous (MulAut.conjNormal d : A → A) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hdiff : Continuous (conjugationDifference A (s γ)) := by
    change Continuous (fun a : A => MulAut.conjNormal (s γ) a / a)
    exact (hconj (s γ)).div' continuous_id
  have hNclosed : IsClosed (N : Set A) := by
    change IsClosed (Set.range (conjugationDifference A (s γ)))
    simpa only [Set.image_univ] using (isCompact_univ.image hdiff).isClosed
  have : T2Space (A ⧸ N) := by infer_instance
  let q : A →ₜ* A ⧸ N :=
    { toMonoidHom := QuotientGroup.mk' N
      continuous_toFun := QuotientGroup.continuous_mk }
  let H : Subgroup Γ :=
    { carrier := {g | ∀ a : A, q (T g a) = q a}
      one_mem' := by
        intro a
        rw [map_one, MulAut.one_apply]
      mul_mem' := by
        intro g h hg hh a
        rw [map_mul]
        exact (hg (T h a)).trans (hh a)
      inv_mem' := by
        intro g hg a
        have h := hg ((T g).symm a)
        rw [MulEquiv.apply_symm_apply] at h
        rw [map_inv]
        exact h.symm }
  have hT (a : A) : Continuous (fun g : Γ => T g a) :=
    ((s.continuous.mul continuous_const).mul s.continuous.inv).subtype_mk _
  have hHclosed : IsClosed (H : Set Γ) := by
    have hset : (H : Set Γ) = ⋂ a : A, {g : Γ | q (T g a) = q a} := by
      ext g
      rw [Set.mem_iInter]
      rfl
    rw [hset]
    exact isClosed_iInter fun a => isClosed_eq (q.continuous.comp (hT a)) continuous_const
  have hγH : γ ∈ H := by
    intro a
    have ha : conjugationDifference A (s γ) a ∈ N := ⟨a, rfl⟩
    have hz : q (conjugationDifference A (s γ) a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ha
    change q (T γ a / a) = 1 at hz
    rw [map_div] at hz
    exact div_eq_one.mp hz
  have hHtop : (⊤ : Subgroup Γ) ≤ H := by
    have hle : (Subgroup.closure ({γ} : Set Γ)).topologicalClosure ≤ H :=
      Subgroup.topologicalClosure_minimal _
        ((Subgroup.closure_le H).mpr (fun _ hx => (Set.mem_singleton_iff.mp hx).symm ▸ hγH))
        hHclosed
    change (Subgroup.closure ({γ} : Set Γ)).topologicalClosure = ⊤ at hγ
    rw [hγ] at hle
    exact hle
  have htrivial (g : Γ) (a : A) : q (T g a) = q a := hHtop trivial a
  let a : P → A := fun p =>
    ⟨p * (s (π p))⁻¹, by
      change π (p * (s (π p))⁻¹) = 1
      rw [map_mul, map_inv, hs, mul_inv_cancel]⟩
  have hacont : Continuous a :=
    (continuous_id.mul (s.continuous.comp π.continuous).inv).subtype_mk _
  have haone : a 1 = 1 := by
    apply Subtype.ext
    change (1 : P) * (s (π 1))⁻¹ = 1
    rw [map_one, map_one, inv_one, mul_one]
  have hamul (p r : P) : a (p * r) = a p * T (π p) (a r) := by
    apply Subtype.ext
    change (p * r) * (s (π (p * r)))⁻¹ =
      (p * (s (π p))⁻¹) * (s (π p) * (r * (s (π r))⁻¹) * (s (π p))⁻¹)
    rw [map_mul, map_mul]
    group
  let r : P →ₜ* A ⧸ N :=
    { toFun := fun p => q (a p)
      map_one' := by rw [haone, map_one]
      map_mul' := by
        intro p t
        rw [hamul, map_mul, htrivial]
      continuous_toFun := q.continuous.comp hacont }
  have hrA (b : A) : r (b : P) = q b := by
    change q (a (b : P)) = q b
    congr 1
    apply Subtype.ext
    change (b : P) * (s (π (b : P)))⁻¹ = (b : P)
    have hb : π (b : P) = 1 := b.property
    rw [hb, map_one, inv_one, mul_one]
  apply le_antisymm
  · intro b hb
    have hmk : TopologicalAbelianization.mk P (b : P) = 1 := hb
    have h := congrArg (TopologicalAbelianization.lift r) hmk
    rw [TopologicalAbelianization.lift_apply_mk, map_one, hrA] at h
    exact (QuotientGroup.eq_one_iff b).mp h
  · rintro _ ⟨b, rfl⟩
    change TopologicalAbelianization.mk P
      (s γ * (b : P) * (s γ)⁻¹ / (b : P)) = 1
    simp only [map_div, map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul, div_self']

end ProCGroups.Abelian
