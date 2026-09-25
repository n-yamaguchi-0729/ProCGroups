/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.FiniteGroups.PrimeSigma
import ProCGroups.FiniteGroups.InducedFunctions
import ProCGroups.FiniteGroups.SigmaMonotonicity
import ProCGroups.FiniteGroups.AllFinite
import ProCGroups.FiniteGroups.Classes
import ProCGroups.FiniteGroups.Solvable
import ProCGroups.FiniteGroups.StandardClasses

import ProCGroups.FiniteGroups.PGroupFormation

set_option autoImplicit false

/-!
# Classes of finite groups

This aggregate module exposes the class of all finite groups together with the standard
formations, varieties, and closure properties used to define pro-`C` groups.
-/
