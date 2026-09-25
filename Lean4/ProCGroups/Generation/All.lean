/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.Generation.Basic
import ProCGroups.Generation.Convergence
import ProCGroups.Generation.GeneratorConvergingPairs
import ProCGroups.Generation.QuotientCriteria
import ProCGroups.Generation.QuotientGeneratorConvergingPairs
import ProCGroups.Generation.WordProductsAndClosure

set_option autoImplicit false

/-!
# Topological generation

This aggregate imports the closure-based definition of topological generation,
families converging to the identity, generator/convergence pairs, finite
quotient criteria, and word-product closure results.
-/
