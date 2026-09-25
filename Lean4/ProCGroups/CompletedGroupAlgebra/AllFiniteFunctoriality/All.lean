/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Comap
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.GroupLike
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.InClassNaturality
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Map
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.StageMap
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Surjectivity

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality

This aggregate exports functoriality of the all-finite completed group algebra for continuous group
homomorphisms: inverse-image quotient indices, finite-stage and completed algebra maps, group-like
compatibility, surjectivity, and naturality of the comparison with \(C\)-indexed completions.
-/
