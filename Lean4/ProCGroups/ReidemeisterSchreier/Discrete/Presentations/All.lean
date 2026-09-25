/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Automation
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.KernelQuotient
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.All
import ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.All

set_option autoImplicit false

/-!
# Presentation tools for Reidemeister--Schreier rewriting

This aggregate exports equality modulo normal closures, quotient-kernel
presentations, presentation automation, semantic Tietze equivalences, and
verified elementary Tietze scripts.
-/
