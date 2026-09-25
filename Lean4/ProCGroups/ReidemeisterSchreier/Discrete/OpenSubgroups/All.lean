/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.ClassicalGeneratorBasis
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.FreeBasis
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Generators
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.PrefixTree
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Transversals
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Words.All

set_option autoImplicit false

/-!
# Reidemeister Schreier / Discrete / Open Subgroups

This aggregate exposes the discrete open-subgroup development: reduced-word
utilities, right Schreier transversals and generators, prefix trees, and the
resulting free bases.
-/
