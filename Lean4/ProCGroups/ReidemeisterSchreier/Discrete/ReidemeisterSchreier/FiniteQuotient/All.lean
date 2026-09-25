/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedRelators
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedSymbols
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedTau
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Data
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Kernel
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Presentation
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.TargetPresentation.All
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Tau
import ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.WordCertificates

set_option autoImplicit false

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient

This aggregate exposes finite-quotient Schreier data, tau rewriting,
degenerate-symbol elimination, kernel presentations, word certificates, and
the cleaned target-presentation equivalence.
-/
