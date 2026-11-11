/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.Augmentation.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.FunctorialityComposition
public import Nyll.ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.ProfiniteModules.All
public import Nyll.ProCGroups.CompletedGroupAlgebra.Separation
public import Nyll.ProCGroups.CompletedGroupAlgebra.UniversalProperty.All

/-!
# Completed group algebras

Completed group algebras are constructed as inverse limits of finite-quotient group algebras.
The library develops their additive, ring, and topological structures together with projections,
augmentation maps and ideals, finite-stage functoriality, separation, and universal properties for
profinite modules.

The completed carriers are opaque; their compatible-family inverse limits are implementation
models exposed through canonical projections, extensionality, and representation equivalences.
`CanonicalCompletedGroupAlgebraModel` is the specification-level API: its inverse-limit universal
property determines comparison, continuity, density, and uniqueness rather than storing parallel
certificates.

This file is the public aggregate for every maintained `CompletedGroupAlgebra` component.
-/
