/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProP.Zassenhaus.OpenNormal
import ProCGroups.ProP.Zassenhaus.AugmentationFiltration
import ProCGroups.ProP.Zassenhaus.Basic
import ProCGroups.ProP.Zassenhaus.DegreeTwo
import ProCGroups.ProP.Zassenhaus.Depth
import ProCGroups.ProP.Zassenhaus.FiniteAugmentationSquare
import ProCGroups.ProP.Zassenhaus.FiniteDegreeOne
import ProCGroups.ProP.Zassenhaus.FiniteLinearization
import ProCGroups.ProP.Zassenhaus.Functoriality
import ProCGroups.ProP.Zassenhaus.GroupLike
import ProCGroups.ProP.Zassenhaus.Laws

set_option autoImplicit false

/-!
# Zassenhaus filtration

Reader-facing facade for the mod-`p` augmentation and Zassenhaus filtration.
-/


/-!
# Zassenhaus aggregate

Imports every maintained augmentation-filtration and Zassenhaus leaf.
-/
