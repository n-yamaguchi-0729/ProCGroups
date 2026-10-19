/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Topologies.DenseSubgroupPullback
import Nyll.ProCGroups.Topologies.FiniteQuotientLift
import Nyll.ProCGroups.Topologies.Conjugation
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Nyll.ProCGroups.Topologies.FullSubgroupTopology.All
import Nyll.ProCGroups.Topologies.OpenSubgroup
import Nyll.ProCGroups.Topologies.QuotientMaps
import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups
import Nyll.ProCGroups.Topologies.OpenActionKernel
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport
import Nyll.ProCGroups.Topologies.FixedFieldConjugatorStrictTransport

/-!
# Topological-group infrastructure

This aggregate module exposes continuous homomorphisms and equivalences, conjugation, open and
characteristic subgroups, quotient maps, and full subgroup topologies.
-/
