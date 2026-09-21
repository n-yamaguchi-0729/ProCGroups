import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

set_option autoImplicit false

/-!
# The prime-order test for ab-faithfulness

A nonfaithful finite quotient action has a prime-order subgroup in its kernel.
Pulling that subgroup back gives an open layer with prime-order quotient and
trivial action on the topological abelianization of its kernel.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

universe u v

/-- A homomorphism out of a prime-order group is injective exactly when it is nontrivial. -/
theorem injective_iff_ne_one_of_prime_card
    {B : Type u} {A : Type v} [Group B] [Group A]
    (ρ : B →* A) (hB : Nat.Prime (Nat.card B)) :
    Function.Injective ρ ↔ ρ ≠ 1 := by
  let : Fact (Nat.Prime (Nat.card B)) := ⟨hB⟩
  constructor
  · intro hinj htriv
    have hker : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).2 hinj
    have htop : ρ.ker = ⊤ := MonoidHom.ker_eq_top_iff.2 htriv
    have hcard : Nat.card B = 1 := by
      have hsubsingleton : Subsingleton B := by
        refine ⟨fun x y => ?_⟩
        have hx : x = 1 := by
          have hxmem : x ∈ ρ.ker := htop.symm ▸ Subgroup.mem_top x
          exact (show x ∈ (⊥ : Subgroup B) from hker ▸ hxmem)
        have hy : y = 1 := by
          have hymem : y ∈ ρ.ker := htop.symm ▸ Subgroup.mem_top y
          exact (show y ∈ (⊥ : Subgroup B) from hker ▸ hymem)
        exact hx.trans hy.symm
      let : Subsingleton B := hsubsingleton
      exact Nat.card_unique
    exact hB.ne_one hcard
  · intro hnontrivial
    rcases ρ.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff ρ).1 hbot
    · exact False.elim (hnontrivial (MonoidHom.ker_eq_top_iff.1 htop))

/-- A noninjective homomorphism from a finite group has a prime-order subgroup in its kernel. -/
theorem exists_prime_card_subgroup_le_ker_of_not_injective
    {B : Type u} {A : Type v} [Group B] [Finite B] [Group A]
    (ρ : B →* A) (hρ : ¬ Function.Injective ρ) :
    ∃ C : Subgroup B, Nat.Prime (Nat.card C) ∧ C ≤ ρ.ker := by
  have hcard : Nat.card ρ.ker ≠ 1 := by
    intro hcard
    exact hρ ((MonoidHom.ker_eq_bot_iff ρ).1 ((Subgroup.eq_bot_iff_card ρ.ker).2 hcard))
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ρ.ker) p hpdvd
  let D : Subgroup ρ.ker := Subgroup.zpowers x
  let C : Subgroup B := D.map ρ.ker.subtype
  have hCcard : Nat.card C = p := by
    calc
      Nat.card C = Nat.card D :=
        (Nat.card_congr
          (D.equivMapOfInjective ρ.ker.subtype Subtype.val_injective).toEquiv).symm
      _ = orderOf x := Nat.card_zpowers x
      _ = p := hx
  refine ⟨C, hCcard.symm ▸ hp, ?_⟩
  intro b hb
  obtain ⟨d, hd, hdb⟩ := hb
  exact hdb ▸ d.property

/-- A nonfaithful open layer yields an open layer with prime-order quotient and trivial action.
The new open subgroup is constructed in the original ambient group, so the result requires no
additional inheritance assumption on the prime-order test. -/
theorem exists_prime_quotient_trivial_action_of_not_injective
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (H : OpenSubgroup G) (N : OpenNormalSubgroup ↥(H : Subgroup G))
    (hρ : ¬ Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G))))) :
    ∃ J : OpenSubgroup G, ∃ M : OpenNormalSubgroup ↥(J : Subgroup G),
      Nat.Prime (Nat.card (↥(J : Subgroup G) ⧸ (M : Subgroup ↥(J : Subgroup G)))) ∧
      quotientConjugationTopologicalAbelianizationMap
        (G := ↥(J : Subgroup G)) (N := (M : Subgroup ↥(J : Subgroup G))) = 1 := by
  let Q : Type u := ↥(H : Subgroup G) ⧸ (N : Subgroup ↥(H : Subgroup G))
  let : Finite Q :=
    Subgroup.quotient_finite_of_isOpen' (H : Subgroup G)
      (N : Subgroup ↥(H : Subgroup G)) H.isOpen N.toOpenSubgroup.isOpen
  let : DiscreteTopology Q := QuotientGroup.discreteTopology N.toOpenSubgroup.isOpen
  let π : ↥(H : Subgroup G) →ₜ* Q := ProC.OpenNormalSubgroup.quotientProj N
  let ρ : Q →* MulAut (TopologicalAbelianization ↥(N : Subgroup ↥(H : Subgroup G))) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G)))
  obtain ⟨C, hCprime, hCker⟩ :=
    exists_prime_card_subgroup_le_ker_of_not_injective ρ hρ
  let P : OpenSubgroup ↥(H : Subgroup G) :=
    { toSubgroup := C.comap π.toMonoidHom
      isOpen' := (isOpen_discrete (C : Set Q)).preimage π.continuous_toFun }
  let J : OpenSubgroup G :=
    { toSubgroup := (P : Subgroup ↥(H : Subgroup G)).map (H : Subgroup G).subtype
      isOpen' := H.isOpen.isOpenMap_subtype_val _ P.isOpen }
  have hJH : (J : Subgroup G) ≤ (H : Subgroup G) := by
    intro g hg
    obtain ⟨h, hh, hhg⟩ := hg
    exact hhg ▸ h.property
  let j : ↥(J : Subgroup G) →ₜ* ↥(H : Subgroup G) :=
    { toFun := fun g => ⟨g.val, hJH g.property⟩
      map_one' := rfl
      map_mul' := fun g k => rfl
      continuous_toFun :=
        Continuous.subtype_mk continuous_subtype_val (fun g => hJH g.property) }
  have hjP : ∀ g : ↥(J : Subgroup G), j g ∈ (P : Subgroup ↥(H : Subgroup G)) := by
    intro g
    obtain ⟨h, hh, hhg⟩ := g.property
    have heq : h = j g := Subtype.ext hhg
    exact heq ▸ hh
  let q : ↥(J : Subgroup G) →ₜ* C :=
    { toFun := fun g => ⟨π (j g), hjP g⟩
      map_one' := Subtype.ext (map_one (π.comp j))
      map_mul' := fun g k => Subtype.ext (map_mul (π.comp j) g k)
      continuous_toFun :=
        Continuous.subtype_mk (π.continuous_toFun.comp j.continuous_toFun) hjP }
  have hqsurj : Function.Surjective q := by
    intro c
    obtain ⟨h, hh⟩ := ProC.OpenNormalSubgroup.quotientProj_surjective N c.val
    have hhP : h ∈ (P : Subgroup ↥(H : Subgroup G)) := by
      change π h ∈ C
      rw [hh]
      exact c.property
    let g : ↥(J : Subgroup G) := ⟨h.val, ⟨h, hhP, rfl⟩⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hh
  let M : OpenNormalSubgroup ↥(J : Subgroup G) := ProC.OpenNormalSubgroup.ker q
  have hMcard : Nat.card (↥(J : Subgroup G) ⧸ (M : Subgroup ↥(J : Subgroup G))) =
      Nat.card C :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hqsurj).toEquiv
  have hNtoP : ∀ n : ↥(N : Subgroup ↥(H : Subgroup G)),
      n.val ∈ (P : Subgroup ↥(H : Subgroup G)) := by
    intro n
    have hn : π n.val = 1 :=
      (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).2 n.property
    change π n.val ∈ C
    rw [hn]
    exact C.one_mem
  let liftN : ↥(N : Subgroup ↥(H : Subgroup G)) → ↥(J : Subgroup G) :=
    fun n => ⟨n.val.val, ⟨n.val, hNtoP n, rfl⟩⟩
  have hliftN : ∀ n : ↥(N : Subgroup ↥(H : Subgroup G)), liftN n ∈ M := by
    intro n
    change q (liftN n) = 1
    apply Subtype.ext
    exact (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).2 n.property
  have hMtoN : ∀ m : ↥(M : Subgroup ↥(J : Subgroup G)),
      j m.val ∈ (N : Subgroup ↥(H : Subgroup G)) := by
    intro m
    apply (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff (U := N)).1
    exact congrArg Subtype.val (show q m.val = 1 from m.property)
  let e : ↥(M : Subgroup ↥(J : Subgroup G)) ≃ₜ*
      ↥(N : Subgroup ↥(H : Subgroup G)) :=
    { toMulEquiv :=
        { toFun := fun m => ⟨j m.val, hMtoN m⟩
          invFun := fun n => ⟨liftN n, hliftN n⟩
          left_inv := fun m => Subtype.ext (Subtype.ext rfl)
          right_inv := fun n => Subtype.ext (Subtype.ext rfl)
          map_mul' := fun m k => Subtype.ext (map_mul j m.val k.val) }
      continuous_toFun :=
        Continuous.subtype_mk (j.continuous_toFun.comp continuous_subtype_val) hMtoN
      continuous_invFun :=
        Continuous.subtype_mk
          (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
            (fun n => ⟨n.val, hNtoP n, rfl⟩)) hliftN }
  refine ⟨J, M, hMcard.symm ▸ hCprime, ?_⟩
  apply MonoidHom.ext
  intro a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (M : Subgroup ↥(J : Subgroup G)) a
  apply quotientConjugationTopologicalAbelianizationMap_mk_eq_one_iff.2
  intro m
  have htriv : ρ (π (j g)) = 1 := hCker (q g).property
  have hcomm : ((MulAut.conjNormal (j g)) (e m)) * (e m)⁻¹ ∈
      Subgroup.closedCommutator ↥(N : Subgroup ↥(H : Subgroup G)) :=
    (quotientConjugationTopologicalAbelianizationMap_mk_eq_one_iff.1 htriv) (e m)
  have hdown : e.symm (((MulAut.conjNormal (j g)) (e m)) * (e m)⁻¹) ∈
      Subgroup.closedCommutator ↥(M : Subgroup ↥(J : Subgroup G)) :=
    Subgroup.closedCommutator_map_le
      { toMonoidHom := e.symm.toMulEquiv.toMonoidHom
        continuous_toFun := e.symm.continuous_toFun }
      ⟨((MulAut.conjNormal (j g)) (e m)) * (e m)⁻¹, hcomm, rfl⟩
  have heq : e.symm (((MulAut.conjNormal (j g)) (e m)) * (e m)⁻¹) =
      ((MulAut.conjNormal g) m) * m⁻¹ := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  exact heq ▸ hdown

/-- A compact topological group is ab-faithful if and only if every open layer with
prime-order quotient acts nontrivially on the topological abelianization of its kernel. -/
theorem isAbFaithful_iff_prime_order_test
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] :
    IsAbFaithful G ↔
      ∀ H : OpenSubgroup G, ∀ N : OpenNormalSubgroup ↥(H : Subgroup G),
        Nat.Prime (Nat.card (↥(H : Subgroup G) ⧸ (N : Subgroup ↥(H : Subgroup G)))) →
        quotientConjugationTopologicalAbelianizationMap
          (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G))) ≠ 1 := by
  constructor
  · intro hG H N hprime
    exact (injective_iff_ne_one_of_prime_card
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G)))) hprime).1
      (hG H N)
  · intro htest H N
    by_contra hnoninjective
    obtain ⟨J, M, hprime, htriv⟩ :=
      exists_prime_quotient_trivial_action_of_not_injective H N hnoninjective
    exact htest J M hprime htriv

end ProCGroups.FiniteStepSolvableQuotients
