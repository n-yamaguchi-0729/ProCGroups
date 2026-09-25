/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods
import ProCGroups.ProC.Quotients.DescendingClosedSubgroupQuotients
import ProCGroups.ProC.Quotients.LeftQuotientMaps
import ProCGroups.ProC.Quotients.LeftQuotientProjectionSections
import ProCGroups.ProC.Quotients.OpenSubgroupSections

set_option autoImplicit false

/-!
# Quotients and sections of pro-\(C\) groups

This aggregate exports quotient topology results, left-quotient projections, continuous sections
for open and closed subgroups, neighborhood approximation, and inverse systems formed from
descending closed subgroups.
-/
