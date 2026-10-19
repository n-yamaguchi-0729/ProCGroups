/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.GroupTheory.CentralizerNormalizerCommensurator
import Nyll.ProCGroups.GroupTheory.Conjugation
import Nyll.ProCGroups.GroupTheory.FinSubSubModEqFlowSumMulModEqZero
import Nyll.ProCGroups.GroupTheory.FinVertexLawEdgeLawPow
import Nyll.ProCGroups.GroupTheory.FinitePGroupLifts
import Nyll.ProCGroups.GroupTheory.MonoidHomSubfieldUnitsCoeEq
import Nyll.ProCGroups.GroupTheory.MonoidHomMapTransferEqTransferComp
import Nyll.ProCGroups.GroupTheory.MulActionNcardOrbitInterOrbitMulCard
import Nyll.ProCGroups.GroupTheory.RegularWreathQuotient
import Nyll.ProCGroups.GroupTheory.RelativeQuotientCentralizers
import Nyll.ProCGroups.GroupTheory.SemidirectSubgroups
import Nyll.ProCGroups.GroupTheory.SplitSemidirect
import Nyll.ProCGroups.GroupTheory.SubgroupEqMulIndexInfEq
import Nyll.ProCGroups.GroupTheory.Subgroups

/-!
# Group-theoretic tools

This aggregate module exposes results about centralizers, normalizers, commensurators,
conjugation actions on quotients, and quotient-kernel embeddings.
-/
