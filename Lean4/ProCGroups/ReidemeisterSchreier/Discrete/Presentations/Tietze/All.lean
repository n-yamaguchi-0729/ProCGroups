/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Core
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorQuotientMutualMapData
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorReplacement
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

set_option autoImplicit false

/-!
# Tietze equivalences and verified scripts

This aggregate separates semantic presentation equivalence from syntactic
transformations.  The core and generator/relator operation modules construct
certificates; `Tietze.Script` records well-typed elementary move sequences and
their trace and cost.
-/
