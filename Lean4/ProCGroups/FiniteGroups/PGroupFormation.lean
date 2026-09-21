import ProCGroups.FiniteGroups.StandardClasses

set_option autoImplicit false

/-!
# The full formation of finite p-groups

The existing formation, subgroup closure and extension closure proofs supply
the full-formation property used by maximal pro-p residual quotients.
-/

namespace ProCGroups.FiniteGroupClass

/-- Finite p-groups form a full formation, using their established subgroup
and extension closure properties. -/
theorem pGroup_fullFormation (p : ℕ) [Fact p.Prime] : FullFormation (pGroup p) where
  melnikovFormation :=
    { formation := pGroup_formation p
      normalSubgroupClosed := fun N _ hG => pGroup_subgroupClosed p N hG
      extensionClosed := pGroup_extensionClosed p }
  subgroupClosed := pGroup_subgroupClosed p

end ProCGroups.FiniteGroupClass
