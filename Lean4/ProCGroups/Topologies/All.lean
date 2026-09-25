/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.Topologies.Conjugation
import ProCGroups.Topologies.ContinuousMonoidHom
import ProCGroups.Topologies.ContinuousMulEquiv
import ProCGroups.Topologies.FullSubgroupTopology.All
import ProCGroups.Topologies.OpenSubgroup
import ProCGroups.Topologies.QuotientMaps
import ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

set_option autoImplicit false

/-!
# Topological-group infrastructure

This aggregate module exposes continuous homomorphisms and equivalences, conjugation, open and
characteristic subgroups, quotient maps, and full subgroup topologies.
-/
