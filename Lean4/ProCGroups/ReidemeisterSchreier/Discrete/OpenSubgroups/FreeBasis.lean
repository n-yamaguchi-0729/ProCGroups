import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.PrefixTree
import ProCGroups.ReidemeisterSchreier.Quiver
import ProCGroups.ReidemeisterSchreier.Schreier

/-!
# Reidemeister Schreier / Discrete / Open Subgroups / Free Basis

Using the action groupoid and Schreier prefix tree, this module constructs a
free basis indexed by complement edges and transports it to the canonical
type of nontrivial Schreier pairs.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups


/--
The total generator arrows in the action groupoid attached to a chosen free basis are indexed by
a pair consisting of a vertex and a basis element.
-/
noncomputable def FreeGroupBasis.actionGroupoidGeneratorTotalEquiv
    {ι G A : Type u} [Group G] [MulAction G A] (b : FreeGroupBasis ι G) :
    letI : IsFreeGroupoid (CategoryTheory.ActionCategory G A) :=
      FreeGroupBasis.actionGroupoidIsFree b
    Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A)) ≃ A × ι := by
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory G A) :=
    FreeGroupBasis.actionGroupoidIsFree b
  refine
    { toFun := fun e => (e.left.back, e.hom.1)
      invFun := fun ai =>
        { left := show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A) from
            ((ai.1 : A) : CategoryTheory.ActionCategory G A)
          right := show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory G A) from
            ((b ai.2 • ai.1 : A) : CategoryTheory.ActionCategory G A)
          hom := ⟨ai.2, rfl⟩ }
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    cases e with
    | mk left right hom =>
        cases left with
        | mk _ a =>
            cases right with
            | mk _ a' =>
                cases hom with
                | mk i hi =>
                    dsimp
                    cases hi
                    rfl
  · intro ai
    rfl

/--
Complement edges of the symmetrized Schreier prefix tree. These are the canonical indexing
objects for the Schreier free basis.
-/
noncomputable abbrev schreierComplementEdges
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) : Type u := by
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  exact
    ↥(((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ :
        Set (Quiver.Total
          (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)))))

/-- The Schreier basis indexed by complement edges of the prefix tree. -/
noncomputable def schreierComplementEdgesBasis
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroupBasis (schreierComplementEdges (X := X) hT) L := by
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  exact
    (ReidemeisterSchreier.Groupoid.endBasis (schreierPrefixTree (X := X) hT)).map
      (schreierRootEndMulEquiv (X := X) hT)

/--
Auxiliary bridge from nontrivial Schreier pairs to the classical Schreier generator value set.
-/
private noncomputable def nontrivialSchreierPairsEquivSchreierGeneratorSet
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    NontrivialSchreierPair (X := X) hT ≃ ↥(schreierGeneratorSet (X := X) hT) := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let C :
      Set (Quiver.Total
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    ((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ : Set _)
  let toSch : ↑C → ↥(schreierGeneratorSet (X := X) hT) := fun i =>
    ⟨schreierGenerator (X := X) hT (((i.1.left.back : T) : FreeGroup X)) i.1.hom.1,
      by
        refine ⟨
          ((i.1.left.back : T) : FreeGroup X), (i.1.left.back : T).property,
          i.1.hom.1, rfl, ?_⟩
        intro hgen
        exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
            (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
          schreierGenerator_eq_one_implies_mem_prefixTree (X := X) hT i.1.hom hgen)⟩
  let b : FreeGroupBasis ↑C L :=
    (ReidemeisterSchreier.Groupoid.endBasis (schreierPrefixTree (X := X) hT)).map
      (schreierRootEndMulEquiv (X := X) hT)
  have hval : ∀ i : ↑C, (b i : L) = (((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) := by
    intro i
    rw [FreeGroupBasis.map_apply, ReidemeisterSchreier.Groupoid.endBasis_apply]
    have htree : ∀ {a b : IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)}
        (e : a ⟶ b),
        e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b →
          (schreierLabelFunctor (X := X) hT).map (IsFreeGroupoid.of e) = (1 : L) := by
      intro a b e he
      exact schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e he
    have hloop := ReidemeisterSchreier.Groupoid.map_loopOfHom_eq_map
      (T := schreierPrefixTree (X := X) hT)
      (F := schreierLabelFunctor (X := X) hT)
      (hTree := by
        intro a b e he
        exact htree e he)
      (q := IsFreeGroupoid.of i.1.hom)
    let loop := ReidemeisterSchreier.Groupoid.rootLoopOfHom (schreierPrefixTree (X := X) hT)
      (IsFreeGroupoid.of i.1.hom)
    have hrootEq : (schreierRootEndMulEquiv (X := X) hT loop : L) =
        (schreierLabelFunctor (X := X) hT).map loop := by
      apply Subtype.ext
      change loop.1 = (1 : FreeGroup X) * loop.1 * (1 : FreeGroup X)⁻¹
      simp only [one_mul, inv_one, mul_one]
    exact hrootEq.trans <| hloop.trans <| schreierLabelFunctor_map_of (X := X) hT i.1.hom
  have hto_inj : Function.Injective toSch := by
    intro i j hij
    apply b.injective
    have hz : ((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L) =
        ((toSch j : ↥(schreierGeneratorSet (X := X) hT)) : L) := congrArg Subtype.val hij
    have hz_inv : (((toSch i : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) =
        (((toSch j : ↥(schreierGeneratorSet (X := X) hT)) : L)⁻¹) := congrArg Inv.inv hz
    exact (hval i).trans (hz_inv.trans (hval j).symm)
  have hto_surj : Function.Surjective toSch := by
    intro z
    rcases z.2 with ⟨t, ht, x, hz, hne⟩
    let a : CategoryTheory.ActionCategory (FreeGroup X) T :=
      ((⟨t, ht⟩ : T) : CategoryTheory.ActionCategory (FreeGroup X) T)
    let b0 : CategoryTheory.ActionCategory (FreeGroup X) T :=
      (schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T)
    let e :
        ((show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T) from a) ⟶
          b0) :=
      ⟨x, by
        rw [FreeGroup.inverseBasis_apply]
        change (FreeGroup.of x)⁻¹ • (show T from CategoryTheory.ActionCategory.back a) =
          (show T from CategoryTheory.ActionCategory.back b0)
        simpa [a, b0] using
          (schreierTransversalRightCosetAction_smul (X := X) hT (FreeGroup.of x)⁻¹ (⟨t, ht⟩ : T))⟩
    have he_not : ⟨a, b0, e⟩ ∈ C := by
      change ¬ e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b0
      intro he
      have hgen1_inv :
          (schreierGenerator (X := X) hT
            ((show T from CategoryTheory.ActionCategory.back a) : FreeGroup X) e.1)⁻¹ = 1 := by
        have htreeLabel :=
          schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e he
        rw [schreierLabelFunctor_map_of (X := X) hT e] at htreeLabel
        exact htreeLabel
      have hgen1 :
          schreierGenerator (X := X) hT
            ((show T from CategoryTheory.ActionCategory.back a) : FreeGroup X) e.1 = 1 :=
        inv_eq_one.mp hgen1_inv
      exact hne (by simpa [a, e, hz] using hgen1)
    refine ⟨⟨⟨a, b0, e⟩, he_not⟩, ?_⟩
    apply Subtype.ext
    simpa [toSch, a, e] using hz.symm
  let eC : ↑C ≃ ↥(schreierGeneratorSet (X := X) hT) := Equiv.ofBijective toSch ⟨hto_inj, hto_surj⟩
  let ePair :
      ↑C ≃ NontrivialSchreierPair (X := X) hT := by
    let eTotal :
        Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)) ≃
          T × X :=
      FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)
    refine
      { toFun := fun i =>
          ⟨eTotal i.1, by
            intro hgen
            have hgen' :
                schreierGenerator (X := X) hT
                  (((show T from CategoryTheory.ActionCategory.back i.1.left) : T) : FreeGroup X)
                  i.1.hom.1 = 1 := by
              simpa [eTotal, FreeGroupBasis.actionGroupoidGeneratorTotalEquiv] using hgen
            exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
                (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
              schreierGenerator_eq_one_implies_mem_prefixTree (X := X) hT i.1.hom hgen')⟩
        invFun := fun p =>
          let e := eTotal.symm p.1
          ⟨e, by
            intro he
            have htreeLabel :=
              schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e.hom
                (show e.hom ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)
                    e.left e.right from he)
            rw [schreierLabelFunctor_map_of (X := X) hT e.hom] at htreeLabel
            have hgen' :
                schreierGenerator (X := X) hT
                  (((show T from CategoryTheory.ActionCategory.back e.left) : T) : FreeGroup X)
                  e.hom.1 = 1 := inv_eq_one.mp htreeLabel
            have hgen'' :
                schreierGenerator (X := X) hT
                  (((eTotal e).1 : T) : FreeGroup X) (eTotal e).2 = 1 := by
              simpa [eTotal, FreeGroupBasis.actionGroupoidGeneratorTotalEquiv] using hgen'
            rw [eTotal.apply_symm_apply p.1] at hgen''
            exact p.2 hgen''⟩
        left_inv := by
          intro i
          apply Subtype.ext
          simp only [Equiv.symm_apply_apply, eTotal]
        right_inv := by
          intro p
          apply Subtype.ext
          simp only [ne_eq, Equiv.apply_symm_apply, eTotal]}
  exact ePair.symm.trans eC

/-- Complement edges are equivalent to nontrivial Schreier pairs. -/
noncomputable def schreierComplementEdgesEquivNontrivialPairs
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    schreierComplementEdges (X := X) hT ≃ NontrivialSchreierPair (X := X) hT := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let C :
      Set (Quiver.Total
        (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    ((Quiver.wideSubquiverEquivSetTotal <|
      Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT))ᶜ : Set _)
  change ↑C ≃ NontrivialSchreierPair (X := X) hT
  let eTotal :
      Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T)) ≃
        T × X :=
    FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)
  refine
    { toFun := fun i =>
        ⟨eTotal i.1, by
          intro hgen
          have hgen' :
              schreierGenerator (X := X) hT
                (((show T from CategoryTheory.ActionCategory.back i.1.left) : T) : FreeGroup X)
                i.1.hom.1 = 1 := by
            simpa [eTotal, FreeGroupBasis.actionGroupoidGeneratorTotalEquiv] using hgen
          exact i.2 (show i.1 ∈ Quiver.wideSubquiverEquivSetTotal
              (Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)) from
            (schreierGenerator_eq_one_iff_mem_prefixTree (X := X) (hT := hT) (e := i.1.hom)).1
                hgen')⟩
      invFun := fun p =>
        let e := eTotal.symm p.1
        ⟨e, by
          intro he
          have hgen' :
              schreierGenerator (X := X) hT
                (((show T from CategoryTheory.ActionCategory.back e.left) : T) : FreeGroup X)
                e.hom.1 = 1 :=
            (schreierGenerator_eq_one_iff_mem_prefixTree (X := X) (hT := hT) (e := e.hom)).2
              (show e.hom ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT)
                  e.left e.right from he)
          have hgen'' :
              schreierGenerator (X := X) hT
                (((eTotal e).1 : T) : FreeGroup X) (eTotal e).2 = 1 := by
            simpa [eTotal, FreeGroupBasis.actionGroupoidGeneratorTotalEquiv] using hgen'
          rw [eTotal.apply_symm_apply p.1] at hgen''
          exact p.2 hgen''⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp only [Equiv.symm_apply_apply, eTotal]
      right_inv := by
        intro p
        apply Subtype.ext
        simp only [ne_eq, Equiv.apply_symm_apply, eTotal]}

/--
The Schreier free basis indexed by nontrivial Schreier pairs. This is the preferred
Schreier-basis formulation; the classical value-set basis is a reindexing of this one.
-/
noncomputable def nontrivialSchreierPairBasis
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroupBasis (NontrivialSchreierPair (X := X) hT) L :=
  (schreierComplementEdgesBasis (X := X) hT).reindex
    (schreierComplementEdgesEquivNontrivialPairs (X := X) hT)

/-- The free group equivalence obtained directly from the preferred pair-indexed Schreier basis. -/
noncomputable def nontrivialSchreierPairBasisEquiv
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroup (NontrivialSchreierPair (X := X) hT) ≃* L :=
  (nontrivialSchreierPairBasis (X := X) hT).repr.symm

/--
The preferred pair-indexed basis equivalence sends each free generator to its Schreier basis
element.
-/
@[simp] theorem nontrivialSchreierPairBasisEquiv_of
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (p : NontrivialSchreierPair (X := X) hT) :
    nontrivialSchreierPairBasisEquiv (X := X) hT (FreeGroup.of p) =
      nontrivialSchreierPairBasis (X := X) hT p := by
  apply (nontrivialSchreierPairBasis (X := X) hT).repr.injective
  calc
    (nontrivialSchreierPairBasis (X := X) hT).repr
        (nontrivialSchreierPairBasisEquiv (X := X) hT (FreeGroup.of p))
        = FreeGroup.of p := by simp only [nontrivialSchreierPairBasisEquiv,
            MulEquiv.apply_symm_apply]
    _ = (nontrivialSchreierPairBasis (X := X) hT).repr
        (nontrivialSchreierPairBasis (X := X) hT p) :=
      (FreeGroupBasis.repr_apply_coe (nontrivialSchreierPairBasis (X := X) hT) p).symm

/--
The Reidemeister--Schreier equivalence is evaluated by the chosen nontrivial Schreier pair and
its associated generator.
-/
private theorem nontrivialSchreierPairsEquivSchreierGeneratorSet_apply
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (p : NontrivialSchreierPair (X := X) hT) :
    ((nontrivialSchreierPairsEquivSchreierGeneratorSet (X := X) hT p :
        ↥(schreierGeneratorSet (X := X) hT)) : L) =
      schreierGenerator (X := X) hT ((p.1.1 : T) : FreeGroup X) p.1.2 := by
  rfl

/-- The Schreier-generator map is injective on nontrivial Schreier pairs. -/
theorem schreierGenerator_injective_of_nontrivial
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Function.Injective
      (nontrivialSchreierPairGenerator (X := X) hT) := by
  intro p q hpq
  apply (nontrivialSchreierPairsEquivSchreierGeneratorSet (X := X) hT).injective
  apply Subtype.ext
  simpa [nontrivialSchreierPairsEquivSchreierGeneratorSet_apply,
    nontrivialSchreierPairGenerator] using hpq

/-- A right Schreier transversal has cardinality equal to the corresponding right-coset index. -/
theorem natCard_schreierTransversal_eq_index
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card T = Nat.card (Quotient (QuotientGroup.rightRel L)) := by
  exact Nat.card_congr hT.1.rightQuotientEquiv.symm

/--
The direct combinatorial count of complement edges in the Schreier prefix tree: all labelled
edges minus tree edges.
-/
theorem natCard_schreierComplementEdges_eq_rankTransform_direct
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite T]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (schreierComplementEdges (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
  classical
  letI := schreierTransversalRightCosetAction (X := X) hT
  letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
  let Ttree :
      WideSubquiver
        (Quiver.Symmetrify
          (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))) :=
    schreierPrefixTree (X := X) hT
  letI : Quiver.Arborescence Ttree := by
    dsimp [Ttree]
    infer_instance
  let totalGen :=
    Quiver.Total (IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T))
  let covered : Set totalGen :=
    Quiver.wideSubquiverEquivSetTotal (Quiver.wideSubquiverSymmetrify Ttree)
  let rootT : T := ⟨(1 : FreeGroup X), hT.2.1⟩
  let root : CategoryTheory.ActionCategory (FreeGroup X) T :=
    CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T rootT
  have hroot : Quiver.root Ttree = root := by
    change root = root
    rfl
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype T := Fintype.ofFinite T
  haveI : Finite (CategoryTheory.ActionCategory (FreeGroup X) T) :=
    Finite.of_equiv T (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T)
  haveI : Finite Ttree :=
    Finite.of_equiv (CategoryTheory.ActionCategory (FreeGroup X) T)
      (show _ ≃ Ttree from Equiv.refl _)
  haveI : Finite totalGen :=
    Finite.of_equiv (T × X)
      (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv (FreeGroup.inverseBasis X)).symm
  letI : Fintype totalGen := Fintype.ofFinite totalGen
  letI : Fintype (schreierComplementEdges (X := X) hT) :=
    Fintype.ofFinite (schreierComplementEdges (X := X) hT)
  letI : Fintype {e : totalGen // e ∈ covered} :=
    Fintype.ofFinite {e : totalGen // e ∈ covered}
  letI : Fintype {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root} :=
    Fintype.ofFinite {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root}
  letI : Fintype {v : Ttree // v ≠ Quiver.root Ttree} :=
    Fintype.ofFinite {v : Ttree // v ≠ Quiver.root Ttree}
  haveI : Finite (Quiver.Total Ttree) :=
    Finite.of_equiv {v : Ttree // v ≠ Quiver.root Ttree}
      (Quiver.Arborescence.totalEquivNonRoot Ttree).symm
  letI : Fintype (Quiver.Total Ttree) := Fintype.ofFinite (Quiver.Total Ttree)
  have hYcard :
      Fintype.card (schreierComplementEdges (X := X) hT) =
        Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered} := by
    change
      Fintype.card {e : totalGen // e ∈ ((covered : Set totalGen)ᶜ)} =
        Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered}
    simpa only [Set.mem_compl_iff] using
      (Fintype.card_subtype_compl (fun e : totalGen => e ∈ covered) :
        Fintype.card {e : totalGen // ¬ e ∈ covered} =
          Fintype.card totalGen - Fintype.card {e : totalGen // e ∈ covered})
  have hTotal :
      Fintype.card totalGen = Fintype.card T * Fintype.card X := by
    simpa [totalGen, Fintype.card_prod] using
      Fintype.card_congr
        (FreeGroupBasis.actionGroupoidGeneratorTotalEquiv
          (ι := X) (G := FreeGroup X) (A := T) (FreeGroup.inverseBasis X))
  let eObjNonRoot :
      {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root} ≃
        {t : T // t ≠ rootT} := {
    toFun := fun a => ⟨(CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T).symm a.1, by
      intro h
      apply a.2
      simpa [root] using congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T) h⟩
    invFun := fun t => ⟨CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T t.1, by
      intro h
      apply t.2
      simpa [root] using
        congrArg (CategoryTheory.ActionCategory.objEquiv (FreeGroup X) T).symm h⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp only [ne_eq, Equiv.apply_symm_apply]
    right_inv := by
      intro t
      apply Subtype.ext
      simp only [ne_eq, Equiv.symm_apply_apply]}
  haveI : Subsingleton {t : T // t = rootT} :=
    ⟨fun t t' => Subtype.ext (by simp only [t.property, t'.property])⟩
  have hOne :
      Fintype.card {t : T // t = rootT} = 1 := by
    exact Fintype.card_ofSubsingleton (⟨rootT, rfl⟩ : {t : T // t = rootT})
  have hTcompl :
      Fintype.card {t : T // t ≠ rootT} = Fintype.card T - 1 := by
    calc
      Fintype.card {t : T // t ≠ rootT}
          = Fintype.card T - Fintype.card {t : T // t = rootT} := by
              exact Fintype.card_subtype_compl (fun t : T => t = rootT)
      _ = Fintype.card T - 1 := by rw [hOne]
  have hNonRoot :
      Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} = Fintype.card T - 1 := by
    let eRootNonRoot :
        {v : Ttree // v ≠ Quiver.root Ttree} ≃
          {a : CategoryTheory.ActionCategory (FreeGroup X) T // a ≠ root} := {
      toFun v := ⟨v.1, fun hv => v.2 (hv.trans hroot.symm)⟩
      invFun a := ⟨a.1, fun ha => a.2 (ha.trans hroot)⟩
      left_inv v := by
        apply Subtype.ext
        rfl
      right_inv a := by
        apply Subtype.ext
        rfl }
    exact (Fintype.card_congr eRootNonRoot).trans
      ((Fintype.card_congr eObjNonRoot).trans hTcompl)
  have hCovered :
      Fintype.card {e : totalGen // e ∈ covered} = Fintype.card T - 1 := by
    calc
      Fintype.card {e : totalGen // e ∈ covered}
          = Fintype.card (Quiver.Total Ttree) := by
              simpa [totalGen, covered] using
                Fintype.card_congr (Quiver.coveredArrowEquivTotal Ttree)
      _ = Fintype.card {v : Ttree // v ≠ Quiver.root Ttree} := by
            simpa using Fintype.card_congr (Quiver.Arborescence.totalEquivNonRoot Ttree)
      _ = Fintype.card T - 1 := hNonRoot
  have hYcalcF :
      Fintype.card (schreierComplementEdges (X := X) hT) =
        Fintype.card T * Fintype.card X - (Fintype.card T - 1) := by
    rw [hYcard, hTotal, hCovered]
  have hYcalc :
      Nat.card (schreierComplementEdges (X := X) hT) =
        Nat.card T * Nat.card X - (Nat.card T - 1) := by
    simpa [Nat.card_eq_fintype_card] using hYcalcF
  by_cases hX0 : Nat.card X = 0
  · have hX0F : Fintype.card X = 0 := by
      simpa [Nat.card_eq_fintype_card] using hX0
    calc
      Nat.card (schreierComplementEdges (X := X) hT)
          = Nat.card T * Nat.card X - (Nat.card T - 1) := hYcalc
      _ = 0 := by simp only [Nat.card_eq_fintype_card, hX0F, mul_zero, zero_tsub]
      _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
            simp only [Schreier.rankTransform, Nat.card_eq_fintype_card, hX0F, ↓reduceIte]
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hX0
    rw [hr] at hYcalc ⊢
    calc
      Nat.card (schreierComplementEdges (X := X) hT)
          = Nat.card T * (r + 1) - (Nat.card T - 1) := hYcalc
      _ = Nat.card T * r + Nat.card T - (Nat.card T - 1) := by
            rw [Nat.mul_succ]
      _ = Nat.card T * r + (Nat.card T - (Nat.card T - 1)) := by
            rw [Nat.add_sub_assoc (Nat.sub_le _ _)]
      _ = Nat.card T * r + 1 := by
            have hTpos : 0 < Nat.card T := by
              simpa [Nat.card_eq_fintype_card] using
                (Fintype.card_pos_iff.mpr ⟨rootT⟩)
            obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hTpos)
            rw [hn]
            simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, add_tsub_cancel_left]
      _ = 1 + Nat.card T * r := by
            rw [Nat.add_comm]
      _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (r + 1) (Nat.card T) := by
            rw [_root_.ReidemeisterSchreier.Schreier.rankTransform_succ]

/--
The preferred pair-indexed generator type has cardinality equal to the Schreier rank-transform
count.
-/
theorem natCard_nontrivialSchreierPairs_eq_rankTransform_direct
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite T]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (NontrivialSchreierPair (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) := by
  calc
    Nat.card (NontrivialSchreierPair (X := X) hT)
        = Nat.card (schreierComplementEdges (X := X) hT) := by
            exact Nat.card_congr
              (schreierComplementEdgesEquivNontrivialPairs (X := X) hT).symm
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) :=
        natCard_schreierComplementEdges_eq_rankTransform_direct (X := X) (L := L) hT

/--
The number of nontrivial Schreier pairs equals the Schreier rank-transform count, with the index
written as the usual left-coset quotient.
-/
theorem natCard_nontrivialSchreierPairs_eq_rankTransform
    {X : Type u} [DecidableEq X] [Finite X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    [Finite (FreeGroup X ⧸ L)]
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Nat.card (NontrivialSchreierPair (X := X) hT) =
      _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (FreeGroup X ⧸
          L)) := by
  classical
  haveI : Finite (Quotient (QuotientGroup.rightRel L)) :=
    Finite.of_equiv (FreeGroup X ⧸ L)
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel L).symm
  haveI : Finite T :=
    Finite.of_equiv (Quotient (QuotientGroup.rightRel L)) hT.1.rightQuotientEquiv
  have hTcard :
      Nat.card T = Nat.card (FreeGroup X ⧸ L) := by
    calc
      Nat.card T = Nat.card (Quotient (QuotientGroup.rightRel L)) := by
        exact (Nat.card_congr hT.1.rightQuotientEquiv).symm
      _ = Nat.card (FreeGroup X ⧸ L) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel L)
  calc
    Nat.card (NontrivialSchreierPair (X := X) hT)
        = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card T) :=
            natCard_nontrivialSchreierPairs_eq_rankTransform_direct (X := X) (L := L) hT
    _ = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (FreeGroup X ⧸
        L)) := by
          rw [hTcard]

/--
A finite-index subgroup of a free group admits a free basis of Schreier-transformed cardinality.
-/
theorem exists_freeBasis_subgroupOfFreeGroup_of_rankTransform
    {X : Type u} {L : Subgroup (FreeGroup X)} [Finite X] [Finite (FreeGroup X ⧸ L)] :
    ∃ Y : Type u, Nonempty (FreeGroupBasis Y L) ∧
      Nat.card Y = _root_.ReidemeisterSchreier.Schreier.rankTransform
        (Nat.card X) (Nat.card (FreeGroup X ⧸ L)) := by
  classical
  rcases exists_rightSchreierTransversal L with ⟨T, hT⟩
  exact ⟨NontrivialSchreierPair (X := X) hT,
    ⟨nontrivialSchreierPairBasis (X := X) hT⟩,
    natCard_nontrivialSchreierPairs_eq_rankTransform (X := X) hT⟩


end ReidemeisterSchreier.Discrete.OpenSubgroups
