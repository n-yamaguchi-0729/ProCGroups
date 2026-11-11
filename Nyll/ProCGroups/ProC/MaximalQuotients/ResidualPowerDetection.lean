/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualFiniteDescent
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Detection of the pro-Sigma residual core by powers

Finite groups annihilated by a Sigma-number lie in the finite Sigma class.
Conversely, an element admitting an n-th root for every positive Sigma-number
vanishes in every finite Sigma quotient of every pro-Sigma quotient, hence
belongs to the actual residual core.
-/

@[expose] public section

namespace ProCGroups

universe u v

/-- Cauchy's theorem detects every prime divisor of a finite group's order
among the prime divisors of an annihilating exponent. -/
theorem FiniteGroupClass.sigmaGroup_of_pow_eq_one
    {H : Type u} [Group H] [Finite H] (sigma : Set ℕ) (n : ℕ)
    (hn : FiniteGroupClass.IsSigmaNumber sigma n) (hpow : ∀ x : H, x ^ n = 1) :
    FiniteGroupClass.sigmaGroup sigma H := by
  refine ⟨inferInstance, ?_⟩
  intro p hp hnot hdiv
  have _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdiv
  have hd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one (hpow x)
  rw [hx] at hd
  exact hn p hp hnot hd

namespace ProC

/-- The residual core is killed by any continuous finite target whose exponent
is a Sigma-number, even when source and target have different universes. -/
theorem proCResidualCore_le_ker_of_finite_exponent
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [Finite H]
    (sigma : Set ℕ) (phi : G →ₜ* H) (n : ℕ)
    (hn : FiniteGroupClass.IsSigmaNumber sigma n) (hpow : ∀ x : H, x ^ n = 1) :
    proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G ≤ phi.toMonoidHom.ker := by
  let N : Subgroup G := phi.toMonoidHom.ker
  have hN : IsClosed (N : Set G) := ContinuousMonoidHom.isClosed_ker phi
  let e : (G ⧸ N) ≃* phi.toMonoidHom.range :=
    QuotientGroup.quotientKerEquivRange phi.toMonoidHom
  have _ : Finite (G ⧸ N) := Finite.of_equiv phi.toMonoidHom.range e.symm.toEquiv
  have hclass : FiniteGroupClass.sigmaGroup sigma (G ⧸ N) :=
    FiniteGroupClass.sigmaGroup_of_pow_eq_one sigma n hn (fun q => by
      apply e.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      exact hpow (e q).1)
  have hbasis : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) (G ⧸ N) :=
    HasOpenNormalBasisInClass.of_finite_discrete
      (FiniteGroupClass.sigmaGroup_quotientClosed sigma) hclass
  exact proCResidualCore_le_of_proCQuotient N hN hbasis

/-- An element having all positive Sigma-number roots lies in the actual
pro-Sigma residual core. No comparison of quotients is an extra hypothesis. -/
theorem mem_proCResidualCore_of_forall_sigmaPower
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (sigma : Set ℕ) (g : G)
    (hg : ∀ n : ℕ, 0 < n → FiniteGroupClass.IsSigmaNumber sigma n →
      ∃ a : G, a ^ n = g) :
    g ∈ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G := by
  rw [proCResidualCore, Subgroup.mem_sInf]
  intro N hN
  obtain ⟨U, rfl⟩ := hN
  have _ : IsClosed (U.toSubgroup : Set G) := U.isClosed'
  apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) g).mp
  apply U.quotient_hasOpenNormalBasisInClass.eq_of_forall_openNormalSubgroupInClass_quotient_eq
  intro V
  let Q := (G ⧸ U.toSubgroup) ⧸ (V.1 : Subgroup (G ⧸ U.toSubgroup))
  have _ : Finite Q := V.2.1
  let pi : G →* Q :=
    (QuotientGroup.mk' (V.1 : Subgroup (G ⧸ U.toSubgroup))).comp
      (QuotientGroup.mk' U.toSubgroup)
  obtain ⟨a, ha⟩ := hg (Nat.card Q) Nat.card_pos V.2.2
  change pi g = 1
  rw [← ha, map_pow]
  exact pow_card_eq_one'

/-- A continuous epimorphism from a compact pro-Sigma group preserves the
Sigma basis in a different carrier universe. -/
private theorem sigmaBasis_of_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [T2Space H]
    (sigma : Set ℕ)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) H := by
  intro W hW h1W
  obtain ⟨V, hVW, hV⟩ := hG (f ⁻¹' W) (hW.preimage f.continuous_toFun)
    (by simpa only [Set.mem_preimage, map_one] using h1W)
  let U := OpenNormalSubgroup.map f
    (ContinuousMonoidHom.isOpenMap_of_surjective_compact_t2 f hf) hf V
  have hVU : (V : Subgroup G) ≤ (U : Subgroup H).comap f.toMonoidHom :=
    fun x hx => ⟨x, hx, rfl⟩
  let q := QuotientGroup.map (V : Subgroup G) (U : Subgroup H) f.toMonoidHom hVU
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective (V : Subgroup G) (U : Subgroup H) f.toMonoidHom
      ((QuotientGroup.mk'_surjective (U : Subgroup H)).comp hf) hVU
  have : Finite (G ⧸ (V : Subgroup G)) := hV.1
  refine ⟨U, ?_, Finite.of_surjective q hq, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hVW hx
  · exact FiniteGroupClass.IsSigmaNumber.of_dvd hV.2 (Subgroup.card_dvd_of_surjective hq)

private theorem map_sigmaResidualCore_eq_of_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (sigma : Set ℕ) (f : G →ₜ* H) (hf : Function.Surjective f) :
    (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G).map f.toMonoidHom =
      proCResidualCore (FiniteGroupClass.sigmaGroup sigma) H := by
  have : CompactSpace H := Function.Surjective.compactSpace f.continuous_toFun hf
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  let N := R.map f.toMonoidHom
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply (mem_proCResidualCore_iff_finite_quotients
      (FiniteGroupClass.sigmaGroup_fullFormation sigma) (f x)).mpr
    intro Q _ _ _ hQ q _
    have : Finite Q := hQ.1
    have hker := proCResidualCore_le_ker_of_finite_exponent sigma (q.comp f)
      (Nat.card Q) hQ.2 (fun x => pow_card_eq_one' (x := x))
    exact hker hx
  · have : N.Normal := Subgroup.Normal.map (inferInstance : R.Normal) f.toMonoidHom hf
    have hN : IsClosed (N : Set H) :=
      ((proCResidualCore_isClosed (FiniteGroupClass.sigmaGroup sigma) G).isCompact.image
        f.continuous_toFun).isClosed
    have hRN : R ≤ N.comap f.toMonoidHom := fun x hx => ⟨x, hx, rfl⟩
    let q := QuotientGroup.mapₜ R N f hRN
    have hq : Function.Surjective q :=
      QuotientGroup.map_surjective_of_surjective R N f.toMonoidHom
        ((QuotientGroup.mk'_surjective N).comp hf) hRN
    exact proCResidualCore_le_of_proCQuotient N hN
      (sigmaBasis_of_surjective sigma
        (proCResidualCoreQuotient_hasOpenNormalBasisInClass
          (FiniteGroupClass.sigmaGroup_formation sigma)) q hq)

/-- The residual core for a Sigma class maps onto the residual core of the
image, allowing the source and target to have different universes. -/
theorem map_sigmaResidualCore_eq_rangeCore
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (sigma : Set ℕ) (f : G →ₜ* H) :
    (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G).map f.toMonoidHom =
      (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) f.toMonoidHom.range).map
        f.toMonoidHom.range.subtype := by
  let q := ContinuousMonoidHom.rangeRestrict f
  have h := congrArg
    (fun S : Subgroup f.toMonoidHom.range => S.map f.toMonoidHom.range.subtype)
    (map_sigmaResidualCore_eq_of_surjective sigma q f.toMonoidHom.rangeRestrict_surjective)
  rw [Subgroup.map_map] at h
  change (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G).map
    (f.toMonoidHom.range.subtype.comp f.toMonoidHom.rangeRestrict) = _ at h
  rwa [MonoidHom.subtype_comp_rangeRestrict] at h

end ProC
end ProCGroups
