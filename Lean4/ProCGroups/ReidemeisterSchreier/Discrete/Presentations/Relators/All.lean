/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Basic
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Congruence
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.FreeGroupLift
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Operations
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Presentation

set_option autoImplicit false

/-!
# Relator toolkit

This aggregate module exposes the relator predicates, congruence constructions,
free-group lifting lemmas, word operations, and presentation-level results used
by the discrete Reidemeister--Schreier development.
-/
