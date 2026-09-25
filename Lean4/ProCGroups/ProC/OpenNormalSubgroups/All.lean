/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
import ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
import ProCGroups.ProC.OpenNormalSubgroups.CountableChains
import ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.ProC.OpenNormalSubgroups.Separation

set_option autoImplicit false

/-!
# Open normal subgroups of pro-\(C\) groups

This aggregate collects the finite quotient, separation, basis, countable-chain, filtered-family,
closed-commutator, and inverse-limit APIs built from open normal subgroups.
-/
