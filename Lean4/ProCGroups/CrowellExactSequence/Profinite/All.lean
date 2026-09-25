/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.CrowellExactSequence.Profinite.BlanchfieldLyndon
import ProCGroups.CrowellExactSequence.Profinite.ContinuousMagnus.All
import ProCGroups.CrowellExactSequence.Profinite.Exactness
import ProCGroups.CrowellExactSequence.Profinite.FreeExactness
import ProCGroups.CrowellExactSequence.Profinite.KernelBoundary
import ProCGroups.CrowellExactSequence.Profinite.KernelInjectivity
import ProCGroups.CrowellExactSequence.Profinite.MainTheorem
import ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.All

set_option autoImplicit false

/-!
# Profinite Crowell exact sequence

This exhaustive aggregate exposes the relation-reflection support, continuous Magnus criterion,
and assembled profinite Crowell--Blanchfield--Lyndon sequence.
-/
