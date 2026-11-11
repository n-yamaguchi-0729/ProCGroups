/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.FreeProducts.Construction

/-!
# Unit, exchange, and associativity for constructed free pro-C products

These comparisons use the concrete finite-diagram construction. Their equations specify
the maps on the original factors, and topological generation proves the inverse identities.
-/

@[expose] public section

namespace ProCGroups.FreeProducts

universe u

variable (C : FiniteGroupClass.{u})
variable (hForm : FiniteGroupClass.Formation C) (hHer : FiniteGroupClass.Hereditary C)
variable (A B D : Type u)
variable [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
  [Group D] [TopologicalSpace D]

/-- The chosen extension from the concrete product takes the prescribed value on the left. -/
theorem lift_inl_apply
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProC.HasOpenNormalBasisInClass C K) (f : A →ₜ* K) (g : B →ₜ* K) (a : A) :
    (isFreeProCProduct C A B hForm hHer).lift hK f g (inl C A B a) = f a :=
  DFunLike.congr_fun ((isFreeProCProduct C A B hForm hHer).lift_left hK f g) a

/-- The chosen extension from the concrete product takes the prescribed value on the right. -/
theorem lift_inr_apply
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProC.HasOpenNormalBasisInClass C K) (f : A →ₜ* K) (g : B →ₜ* K) (b : B) :
    (isFreeProCProduct C A B hForm hHer).lift hK f g (inr C A B b) = g b :=
  DFunLike.congr_fun ((isFreeProCProduct C A B hForm hHer).lift_right hK f g) b

include hForm hHer in
/-- The concrete product in the opposite order has the exchanged universal property. -/
theorem isFreeProCProduct_swap :
    IsFreeProCProduct (C := C) (inr C B A) (inl C B A) where
  hasOpenNormalBasisInClass := freeProduct_hasOpenNormalBasisInClass C B A hForm hHer
  existsUnique_lift := by
    intro K _ _ _ _ _ _ hK f g
    obtain ⟨φ, hφ, huniq⟩ :=
      (isFreeProCProduct C B A hForm hHer).existsUnique_lift hK g f
    exact ⟨φ, ⟨hφ.2, hφ.1⟩, fun ψ hψ => huniq ψ ⟨hψ.2, hψ.1⟩⟩

/-- Exchange of the two factors of the constructed free product. -/
noncomputable def swapEquiv : FreeProduct C A B ≃ₜ* FreeProduct C B A :=
  (isFreeProCProduct C A B hForm hHer).equiv
    (isFreeProCProduct_swap C hForm hHer A B)

/-- Exchange carries the first factor to the second factor. -/
theorem swapEquiv_inl :
    (swapEquiv C hForm hHer A B : FreeProduct C A B →ₜ* FreeProduct C B A).comp
      (inl C A B) = inr C B A :=
  (isFreeProCProduct C A B hForm hHer).equiv_left
    (isFreeProCProduct_swap C hForm hHer A B)

/-- Exchange carries the second factor to the first factor. -/
theorem swapEquiv_inr :
    (swapEquiv C hForm hHer A B : FreeProduct C A B →ₜ* FreeProduct C B A).comp
      (inr C A B) = inl C B A :=
  (isFreeProCProduct C A B hForm hHer).equiv_right
    (isFreeProCProduct_swap C hForm hHer A B)

section Unit

variable [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
variable [Subsingleton B]
variable (hA : ProC.HasOpenNormalBasisInClass C A)

include hA in
omit [IsTopologicalGroup A] in
/-- A pro-C group itself solves the free-product problem with a trivial right factor. -/
theorem isFreeProCProduct_rightUnit :
    IsFreeProCProduct (C := C) (ContinuousMonoidHom.id A) (1 : B →ₜ* A) where
  hasOpenNormalBasisInClass := hA
  existsUnique_lift := by
    intro K _ _ _ _ _ _ _hK f g
    refine ⟨f, ⟨rfl, ?_⟩, ?_⟩
    · apply ContinuousMonoidHom.ext
      intro b
      change f 1 = g b
      rw [Subsingleton.elim b 1, map_one, map_one]
    · intro φ hφ
      exact hφ.1

/-- A trivial right factor is a unit for a pro-C factor with its given topology. -/
noncomputable def rightUnitEquiv : FreeProduct C A B ≃ₜ* A :=
  (isFreeProCProduct C A B hForm hHer).equiv
    (isFreeProCProduct_rightUnit C A B hA)

/-- The right-unit comparison restricts to the identity on the nontrivial factor. -/
theorem rightUnitEquiv_inl :
    (rightUnitEquiv C hForm hHer A B hA : FreeProduct C A B →ₜ* A).comp
      (inl C A B) = ContinuousMonoidHom.id A :=
  (isFreeProCProduct C A B hForm hHer).equiv_left
    (isFreeProCProduct_rightUnit C A B hA)

/-- The right-unit comparison sends the trivial factor to one. -/
theorem rightUnitEquiv_inr :
    (rightUnitEquiv C hForm hHer A B hA : FreeProduct C A B →ₜ* A).comp
      (inr C A B) = 1 :=
  (isFreeProCProduct C A B hForm hHer).equiv_right
    (isFreeProCProduct_rightUnit C A B hA)

/-- A trivial left factor is also a unit, by exchange and the right-unit comparison. -/
noncomputable def leftUnitEquiv : FreeProduct C B A ≃ₜ* A :=
  (swapEquiv C hForm hHer B A).trans (rightUnitEquiv C hForm hHer A B hA)

/-- The left-unit comparison sends the trivial factor to one. -/
theorem leftUnitEquiv_inl :
    (leftUnitEquiv C hForm hHer A B hA : FreeProduct C B A →ₜ* A).comp
      (inl C B A) = 1 := by
  change (rightUnitEquiv C hForm hHer A B hA : FreeProduct C A B →ₜ* A).comp
    ((swapEquiv C hForm hHer B A : FreeProduct C B A →ₜ* FreeProduct C A B).comp
      (inl C B A)) = 1
  rw [swapEquiv_inl, rightUnitEquiv_inr]

/-- The left-unit comparison restricts to the identity on the nontrivial factor. -/
theorem leftUnitEquiv_inr :
    (leftUnitEquiv C hForm hHer A B hA : FreeProduct C B A →ₜ* A).comp
      (inr C B A) = ContinuousMonoidHom.id A := by
  change (rightUnitEquiv C hForm hHer A B hA : FreeProduct C A B →ₜ* A).comp
    ((swapEquiv C hForm hHer B A : FreeProduct C B A →ₜ* FreeProduct C A B).comp
      (inr C B A)) = ContinuousMonoidHom.id A
  rw [swapEquiv_inr, rightUnitEquiv_inl]

end Unit

/-- The forward association map, formed by two applications of the constructed extension. -/
noncomputable def associate :
    FreeProduct C (FreeProduct C A B) D →ₜ* FreeProduct C A (FreeProduct C B D) :=
  (isFreeProCProduct C (FreeProduct C A B) D hForm hHer).lift
    (freeProduct_hasOpenNormalBasisInClass C A (FreeProduct C B D) hForm hHer)
    ((isFreeProCProduct C A B hForm hHer).lift
      (freeProduct_hasOpenNormalBasisInClass C A (FreeProduct C B D) hForm hHer)
      (inl C A (FreeProduct C B D))
      ((inr C A (FreeProduct C B D)).comp (inl C B D)))
    ((inr C A (FreeProduct C B D)).comp (inr C B D))

/-- The inverse association map, again supplied by the concrete extension property. -/
noncomputable def associateInv :
    FreeProduct C A (FreeProduct C B D) →ₜ* FreeProduct C (FreeProduct C A B) D :=
  (isFreeProCProduct C A (FreeProduct C B D) hForm hHer).lift
    (freeProduct_hasOpenNormalBasisInClass C (FreeProduct C A B) D hForm hHer)
    ((inl C (FreeProduct C A B) D).comp (inl C A B))
    ((isFreeProCProduct C B D hForm hHer).lift
      (freeProduct_hasOpenNormalBasisInClass C (FreeProduct C A B) D hForm hHer)
      ((inl C (FreeProduct C A B) D).comp (inr C A B))
      (inr C (FreeProduct C A B) D))

/-- Forward association preserves the first factor. -/
theorem associate_inl_inl (a : A) :
    associate C hForm hHer A B D (inl C (FreeProduct C A B) D (inl C A B a)) =
      inl C A (FreeProduct C B D) a := by
  simp only [associate, lift_inl_apply C hForm hHer]

/-- Forward association preserves the middle factor. -/
theorem associate_inl_inr (b : B) :
    associate C hForm hHer A B D (inl C (FreeProduct C A B) D (inr C A B b)) =
      inr C A (FreeProduct C B D) (inl C B D b) := by
  simp only [associate, lift_inl_apply C hForm hHer, lift_inr_apply C hForm hHer,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]

/-- Forward association preserves the last factor. -/
theorem associate_inr (d : D) :
    associate C hForm hHer A B D (inr C (FreeProduct C A B) D d) =
      inr C A (FreeProduct C B D) (inr C B D d) := by
  simp only [associate, lift_inr_apply C hForm hHer,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]

/-- Inverse association preserves the first factor. -/
theorem associateInv_inl (a : A) :
    associateInv C hForm hHer A B D (inl C A (FreeProduct C B D) a) =
      inl C (FreeProduct C A B) D (inl C A B a) := by
  simp only [associateInv, lift_inl_apply C hForm hHer,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]

/-- Inverse association preserves the middle factor. -/
theorem associateInv_inr_inl (b : B) :
    associateInv C hForm hHer A B D (inr C A (FreeProduct C B D) (inl C B D b)) =
      inl C (FreeProduct C A B) D (inr C A B b) := by
  simp only [associateInv, lift_inr_apply C hForm hHer, lift_inl_apply C hForm hHer,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]

/-- Inverse association preserves the last factor. -/
theorem associateInv_inr_inr (d : D) :
    associateInv C hForm hHer A B D (inr C A (FreeProduct C B D) (inr C B D d)) =
      inr C (FreeProduct C A B) D d := by
  simp only [associateInv, lift_inr_apply C hForm hHer]

/-- The association maps compose to the identity on the left-associated product. -/
theorem associateInv_comp_associate :
    (associateInv C hForm hHer A B D).comp (associate C hForm hHer A B D) =
      ContinuousMonoidHom.id (FreeProduct C (FreeProduct C A B) D) := by
  apply freeProduct_hom_ext C (FreeProduct C A B) D
  · apply freeProduct_hom_ext C A B
    · apply ContinuousMonoidHom.ext
      intro a
      change associateInv C hForm hHer A B D
        (associate C hForm hHer A B D (inl C (FreeProduct C A B) D (inl C A B a))) = _
      rw [associate_inl_inl C hForm hHer, associateInv_inl C hForm hHer]
      simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
        Function.comp_apply, id_eq]
    · apply ContinuousMonoidHom.ext
      intro b
      change associateInv C hForm hHer A B D
        (associate C hForm hHer A B D (inl C (FreeProduct C A B) D (inr C A B b))) = _
      rw [associate_inl_inr C hForm hHer, associateInv_inr_inl C hForm hHer]
      simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
        Function.comp_apply, id_eq]
  · apply ContinuousMonoidHom.ext
    intro d
    change associateInv C hForm hHer A B D
      (associate C hForm hHer A B D (inr C (FreeProduct C A B) D d)) = _
    rw [associate_inr C hForm hHer, associateInv_inr_inr C hForm hHer]
    simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
      Function.comp_apply, id_eq]

/-- The association maps compose to the identity on the right-associated product. -/
theorem associate_comp_associateInv :
    (associate C hForm hHer A B D).comp (associateInv C hForm hHer A B D) =
      ContinuousMonoidHom.id (FreeProduct C A (FreeProduct C B D)) := by
  apply freeProduct_hom_ext C A (FreeProduct C B D)
  · apply ContinuousMonoidHom.ext
    intro a
    change associate C hForm hHer A B D
      (associateInv C hForm hHer A B D (inl C A (FreeProduct C B D) a)) = _
    rw [associateInv_inl C hForm hHer, associate_inl_inl C hForm hHer]
    simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
      Function.comp_apply, id_eq]
  · apply freeProduct_hom_ext C B D
    · apply ContinuousMonoidHom.ext
      intro b
      change associate C hForm hHer A B D
        (associateInv C hForm hHer A B D (inr C A (FreeProduct C B D) (inl C B D b))) = _
      rw [associateInv_inr_inl C hForm hHer, associate_inl_inr C hForm hHer]
      simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
        Function.comp_apply, id_eq]
    · apply ContinuousMonoidHom.ext
      intro d
      change associate C hForm hHer A B D
        (associateInv C hForm hHer A B D (inr C A (FreeProduct C B D) (inr C B D d))) = _
      rw [associateInv_inr_inr C hForm hHer, associate_inr C hForm hHer]
      simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_id,
        Function.comp_apply, id_eq]

/-- The canonical continuous associativity equivalence of three constructed factors. -/
noncomputable def associator :
    FreeProduct C (FreeProduct C A B) D ≃ₜ* FreeProduct C A (FreeProduct C B D) where
  toFun := associate C hForm hHer A B D
  invFun := associateInv C hForm hHer A B D
  left_inv x := DFunLike.congr_fun (associateInv_comp_associate C hForm hHer A B D) x
  right_inv x := DFunLike.congr_fun (associate_comp_associateInv C hForm hHer A B D) x
  map_mul' := (associate C hForm hHer A B D).map_mul
  continuous_toFun := (associate C hForm hHer A B D).continuous
  continuous_invFun := (associateInv C hForm hHer A B D).continuous

/-- The associator commutes with the first specified inclusion. -/
theorem associator_inl_inl (a : A) :
    associator C hForm hHer A B D (inl C (FreeProduct C A B) D (inl C A B a)) =
      inl C A (FreeProduct C B D) a :=
  associate_inl_inl C hForm hHer A B D a

/-- The associator commutes with the middle specified inclusion. -/
theorem associator_inl_inr (b : B) :
    associator C hForm hHer A B D (inl C (FreeProduct C A B) D (inr C A B b)) =
      inr C A (FreeProduct C B D) (inl C B D b) :=
  associate_inl_inr C hForm hHer A B D b

/-- The associator commutes with the last specified inclusion. -/
theorem associator_inr (d : D) :
    associator C hForm hHer A B D (inr C (FreeProduct C A B) D d) =
      inr C A (FreeProduct C B D) (inr C B D d) :=
  associate_inr C hForm hHer A B D d

end ProCGroups.FreeProducts
