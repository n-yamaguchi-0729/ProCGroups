/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FreeProC.Abelianization
import ProCGroups.FreeProC.Basic
import ProCGroups.FreeProC.CanonicalData
import ProCGroups.FreeProC.Characterization.All
import ProCGroups.FreeProC.Criteria.All
import ProCGroups.FreeProC.FiniteBasis
import ProCGroups.FreeProC.FiniteRankSourceData
import ProCGroups.FreeProC.FinitelyGenerated
import ProCGroups.FreeProC.SolvableQuotients
import ProCGroups.FreeProC.Universe
import ProCGroups.FreeProC.Construction

set_option autoImplicit false

/-!
# Free pro-`C` groups

This aggregate module exposes the construction and universal property of free pro-`C` groups,
finite-basis and finite-generation results, canonical source data, characterizations, and
applications to abelian and solvable quotients.
-/
