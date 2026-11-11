/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Core
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorQuotientMutualMapData
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorReplacement
public import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

/-!
# Tietze equivalences and verified scripts

This aggregate separates semantic presentation equivalence from syntactic
transformations.  The core and generator/relator operation modules construct
certificates; `Tietze.Script` records well-typed elementary move sequences and
their trace and cost.
-/
