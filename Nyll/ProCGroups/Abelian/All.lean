/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.AbelianModPower
import Nyll.ProCGroups.Abelian.AddCommGroupApplyZsmulAddEq
import Nyll.ProCGroups.Abelian.AddCommGroupBasisSmulEq
import Nyll.ProCGroups.Abelian.AddCommGroupMemTorsionBySmulEq
import Nyll.ProCGroups.Abelian.AddCommGroupFiniteNatCardTorsionByLe
import Nyll.ProCGroups.Abelian.AddCommGroupNatCardPrimaryComponentKerAeval
import Nyll.ProCGroups.Abelian.AddCommGroupNatCardTorsionByPowEqPow
import Nyll.ProCGroups.Abelian.AddCommGroupBasisZmodPow
import Nyll.ProCGroups.Abelian.AddMonoidHomNsmulEqZeroApplyEq
import Nyll.ProCGroups.Abelian.AddMonoidHomMemRangeSmulEqZero
import Nyll.ProCGroups.Abelian.AddMonoidHomNatCardKerCompEqMul
import Nyll.ProCGroups.Abelian.CharacterCardinalityTorsionFree
import Nyll.ProCGroups.Abelian.CharacterDetection
import Nyll.ProCGroups.Abelian.FiniteBidual
import Nyll.ProCGroups.Abelian.FiniteCharacterCriterion
import Nyll.ProCGroups.Abelian.FiniteFixedCharacters
import Nyll.ProCGroups.Abelian.FiniteInvariantQuotients
import Nyll.ProCGroups.Abelian.FinsuppListEqSumSingleSubSingle
import Nyll.ProCGroups.Abelian.FullTateCharacters
import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.ProCGroups.Abelian.FullTateModuleMap
import Nyll.ProCGroups.Abelian.FullTateRestriction
import Nyll.ProCGroups.Abelian.PowerQuotientAction
import Nyll.ProCGroups.Abelian.PrimaryDetection
import Nyll.ProCGroups.Abelian.PrimaryTorsion
import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
import Nyll.ProCGroups.Abelian.PrimePowerCharacters
import Nyll.ProCGroups.Abelian.PrimeQuotients
import Nyll.ProCGroups.Abelian.ProfiniteBidual
import Nyll.ProCGroups.Abelian.ProfiniteCharacterCriterion
import Nyll.ProCGroups.Abelian.RestrictedTateModule
import Nyll.ProCGroups.Abelian.RestrictedTatePairingWeights
import Nyll.ProCGroups.Abelian.RestrictedTateTorsionFree
import Nyll.ProCGroups.Abelian.RestrictedTateTransport
import Nyll.ProCGroups.Abelian.RootsOfUnityCharacterCriterion
import Nyll.ProCGroups.Abelian.SubgroupCommutator
import Nyll.ProCGroups.Abelian.SubmoduleFiniteTorsionByPow
import Nyll.ProCGroups.Abelian.SubmoduleNatCardTorsionByQuotientEqPowFinrank
import Nyll.ProCGroups.Abelian.SubtractionMonoidZsmulEqPrime
import Nyll.ProCGroups.Abelian.SubtractionMonoidZsmulEqPrimeNsmul
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationConjugationContinuity
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationLimits
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationQuotientFaithfulness
import Nyll.ProCGroups.Abelian.Transfer
import Nyll.ProCGroups.Abelian.CardTorsionMulDivisible

/-!
# Abelian constructions

This aggregate module exposes topological abelianization, its functoriality, and its compatibility
with inverse limits.
-/
