/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.CountableChains
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation

/-!
# Open normal subgroups of pro-\(C\) groups

This aggregate collects the finite quotient, separation, basis, countable-chain, filtered-family,
closed-commutator, and inverse-limit APIs built from open normal subgroups.
-/
