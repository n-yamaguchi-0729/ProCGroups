/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.MaximalAbelianProP
public import Nyll.ProCGroups.Abelian.PrimePowerCharacters

/-!
# Native finite characters and fixed elements of the actual abelian pro-p quotient

Finite cyclic characters descend through the original topological
abelianization and the original pro-p residual quotient, also when the
fundamental group lives in a larger universe than its coefficients.
Surjectivity of pullback minus identity can therefore be proved on the
original geometric fundamental group and used on its actual abelian pro-p
quotient. The induced endomorphism is the canonical quotient map.
-/

@[expose] public section

noncomputable section

namespace ProCGroups.Abelian.AbelianProPQuotient

open ProCGroups.ProC

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- A finite cyclic p-power character descends through the actual maximal
abelian pro-p quotient, without a same-universe restriction on coefficients. -/
def liftPrimePowerCharacter (n : ℕ)
    (χ : G →ₜ* Multiplicative (ZMod (p ^ n))) :
    AbelianProPQuotient p G →ₜ* Multiplicative (ZMod (p ^ n)) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let B := ULift.{u} (Multiplicative (ZMod (p ^ n)))
  let up : G →ₜ* B :=
    { toFun := fun g => ULift.up (χ g)
      map_one' := ULift.ext χ.map_one
      map_mul' := fun g h => ULift.ext (χ.map_mul g h)
      continuous_toFun := continuous_uliftUp.comp χ.continuous }
  have hP : IsPGroup p B := by
    apply IsPGroup.of_card (n := n)
    simp only [B, Nat.card_eq_fintype_card, Fintype.card_ulift,
      Fintype.card_multiplicative, ZMod.card]
  have hB : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) B := by
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    exact ⟨inferInstance, hP.of_surjective (QuotientGroup.mk' (U : Subgroup B))
      (QuotientGroup.mk'_surjective _)⟩
  let down : B →ₜ* Multiplicative (ZMod (p ^ n)) :=
    { toFun := ULift.down
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := continuous_uliftDown }
  exact down.comp (lift p up hB)

/-- The descended finite character retains the original values. -/
theorem liftPrimePowerCharacter_apply_mk (n : ℕ)
    (χ : G →ₜ* Multiplicative (ZMod (p ^ n))) (g : G) :
    liftPrimePowerCharacter p n χ (mk p G g) = χ g := rfl

/-- An actual finite character equation descends along the canonical
projection and the canonical induced endomorphism. -/
theorem primePower_character_difference_surjective_map
    (F : G →ₜ* G)
    (hsurj : ∀ n : ℕ, 0 < n → Function.Surjective
      (fun χ : G →ₜ* Multiplicative (ZMod (p ^ n)) => χ.comp F / χ)) :
    ∀ n : ℕ, 0 < n → Function.Surjective
      (fun χ : AbelianProPQuotient p G →ₜ* Multiplicative (ZMod (p ^ n)) =>
        χ.comp (map p F) / χ) := by
  intro n hn χ
  obtain ⟨ψ, hψ⟩ := hsurj n hn (χ.comp (mk p G))
  refine ⟨liftPrimePowerCharacter p n ψ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨g, rfl⟩ := surjective_mk p G a
  exact congrArg (fun η : G →ₜ* Multiplicative (ZMod (p ^ n)) => η g) hψ

variable [T2Space G] [TotallyDisconnectedSpace G]

/-- Native cyclic-character difference surjectivity kills fixed points of
the actual abelian pro-p quotient. No quotient comparison is an input. -/
theorem fixed_eq_one_of_native_primePower_character_difference_surjective
    (F : G →ₜ* G)
    (hsurj : ∀ n : ℕ, 0 < n → Function.Surjective
      (fun χ : G →ₜ* Multiplicative (ZMod (p ^ n)) => χ.comp F / χ))
    {a : AbelianProPQuotient p G} (ha : map p F a = a) : a = 1 := by
  by_contra hne
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP
    (hasOpenNormalBasisInClass p G) hne
  obtain ⟨ψ, hψ⟩ := primePower_character_difference_surjective_map p F hsurj n hn χ
  have heval := congrArg
    (fun η : AbelianProPQuotient p G →ₜ* Multiplicative (ZMod (p ^ n)) => η a) hψ
  change ψ (map p F a) / ψ a = χ a at heval
  rw [ha, div_self'] at heval
  exact hχ heval.symm

end ProCGroups.Abelian.AbelianProPQuotient
