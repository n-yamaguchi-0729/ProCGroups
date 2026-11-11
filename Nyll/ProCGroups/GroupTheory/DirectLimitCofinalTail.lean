/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Homomorphisms from a cofinal tail of the original directed system

Maps specified beyond one original index determine a map on the entire
direct limit. Earlier representatives are moved by their actual transition
maps to a common later index. Compatibility proves independence of that
choice and retains the supplied map at every index in the tail.
-/

@[expose] public section

noncomputable section

namespace DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {G : ι → Type*} [∀ i, Monoid (G i)]
  (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G (f · · ·)]
  {C : Type*} [Monoid C] (i₀ : ι)
  (g : ∀ i, i₀ ≤ i → G i →* C)
  (hg : ∀ (i j : ι) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j) (x : G i),
    g i hi x = g j hj (f i j hij x))

/-- A chosen common upper index belonging to the specified cofinal tail. -/
def tailUpper (i : ι) : {j : ι // i ≤ j ∧ i₀ ≤ j} :=
  ⟨(exists_ge_ge i i₀).choose, (exists_ge_ge i i₀).choose_spec⟩

/-- The stage map obtained by moving an original representative into the tail. -/
def tailStageHom (i : ι) : G i →* C :=
  (g (tailUpper i₀ i).val (tailUpper i₀ i).property.2).comp
    (f i (tailUpper i₀ i).val (tailUpper i₀ i).property.1)

omit [Nonempty ι] in
include hg in
private theorem tailStageHom_eq_at (i j : ι) (hj : i₀ ≤ j) (hij : i ≤ j) (x : G i) :
    tailStageHom f i₀ g i x = g j hj (f i j hij x) := by
  let r := tailUpper i₀ i
  obtain ⟨l, hrl, hjl⟩ := exists_ge_ge r.val j
  have hl : i₀ ≤ l := r.property.2.trans hrl
  change g r.val r.property.2 (f i r.val r.property.1 x) = _
  calc
    g r.val r.property.2 (f i r.val r.property.1 x) =
        g l hl (f r.val l hrl (f i r.val r.property.1 x)) :=
      hg r.val l r.property.2 hl hrl _
    _ = g l hl (f i l (hij.trans hjl) x) := by
      rw [DirectedSystem.map_map' f]
    _ = g l hl (f j l hjl (f i j hij x)) := by
      rw [DirectedSystem.map_map' f]
    _ = g j hj (f i j hij x) := (hg j l hj hl hjl _).symm

omit [Nonempty ι] in
include hg in
/-- The chosen stage maps commute with the original directed transitions. -/
theorem tailStageHom_transition (i j : ι) (hij : i ≤ j) (x : G i) :
    tailStageHom f i₀ g i x = tailStageHom f i₀ g j (f i j hij x) := by
  let r := tailUpper i₀ j
  rw [tailStageHom_eq_at f i₀ g hg i r.val r.property.2 (hij.trans r.property.1),
    tailStageHom_eq_at f i₀ g hg j r.val r.property.2 r.property.1,
    DirectedSystem.map_map' f]

/-- A compatible family on a cofinal tail acts on the original direct
limit through its actual transition maps. -/
def tailLift : DirectLimit G f →* C :=
  { toFun := DirectLimit.lift f (fun i => tailStageHom f i₀ g i)
      (tailStageHom_transition f i₀ g hg)
    map_one' := DirectLimit.lift_one (fun i => tailStageHom f i₀ g i)
      (tailStageHom_transition f i₀ g hg)
    map_mul' := DirectLimit.lift_mul (fun i => tailStageHom f i₀ g i)
      (tailStageHom_transition f i₀ g hg) }

/-- Every original representative may be evaluated at any later tail
stage, without changing its image in the target. -/
theorem tailLift_mk_of_le (i j : ι) (hj : i₀ ≤ j) (hij : i ≤ j) (x : G i) :
    tailLift f i₀ g hg ⟦⟨i, x⟩⟧ = g j hj (f i j hij x) :=
  tailStageHom_eq_at f i₀ g hg i j hj hij x

/-- At every stage in the tail the map is exactly the prescribed map. -/
theorem tailLift_mk (i : ι) (hi : i₀ ≤ i) (x : G i) :
    tailLift f i₀ g hg ⟦⟨i, x⟩⟧ = g i hi x := by
  rw [tailLift_mk_of_le f i₀ g hg i i hi le_rfl, DirectedSystem.map_self' f]

/-- Injective original transitions and injective tail maps give an
injective map from the entire original direct limit. -/
theorem tailLift_injective
    (hf : ∀ (i j : ι) (hij : i ≤ j), Function.Injective (f i j hij))
    (hgInjective : ∀ (i : ι) (hi : i₀ ≤ i), Function.Injective (g i hi)) :
    Function.Injective (tailLift f i₀ g hg) := by
  exact DirectLimit.lift_injective f (fun i => tailStageHom f i₀ g i)
    (tailStageHom_transition f i₀ g hg)
    (fun i => (hgInjective (tailUpper i₀ i).val (tailUpper i₀ i).property.2).comp
      (hf i (tailUpper i₀ i).val (tailUpper i₀ i).property.1))

/-- A target covered by the actual tail images is covered by the induced
map on the original direct limit. -/
theorem tailLift_surjective
    (hsurj : ∀ z : C, ∃ (i : ι) (hi : i₀ ≤ i) (x : G i), g i hi x = z) :
    Function.Surjective (tailLift f i₀ g hg) := by
  intro z
  obtain ⟨i, hi, x, hx⟩ := hsurj z
  exact ⟨⟦⟨i, x⟩⟧, (tailLift_mk f i₀ g hg i hi x).trans hx⟩

/-- The prescribed values on a cofinal tail determine the original
direct-limit homomorphism uniquely. -/
theorem tailLift_unique (φ : DirectLimit G f →* C)
    (hφ : ∀ (i : ι) (hi : i₀ ≤ i) (x : G i), φ ⟦⟨i, x⟩⟧ = g i hi x) :
    φ = tailLift f i₀ g hg := by
  apply MonoidHom.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
      let r := tailUpper i₀ i
      have heq : (⟦⟨i, x⟩⟧ : DirectLimit G f) =
          ⟦⟨r.val, f i r.val r.property.1 x⟩⟧ :=
        Quotient.sound (DirectLimit.r_of_le f ⟨i, x⟩ r.val r.property.1)
      rw [heq, hφ r.val r.property.2,
        tailLift_mk f i₀ g hg r.val r.property.2]

end DirectLimit
