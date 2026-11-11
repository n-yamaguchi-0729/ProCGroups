/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.AbelianModPower
public import Nyll.ProCGroups.Abelian.AddCommGroupApplyZsmulAddEq
public import Nyll.ProCGroups.Abelian.AddCommGroupBasisSmulEq
public import Nyll.ProCGroups.Abelian.AddCommGroupMemTorsionBySmulEq
public import Nyll.ProCGroups.Abelian.TorsionPresentation
public import Nyll.ProCGroups.Abelian.AddCommGroupFiniteNatCardTorsionByLe
public import Nyll.ProCGroups.Abelian.AddCommGroupNatCardPrimaryComponentKerAeval
public import Nyll.ProCGroups.Abelian.AddCommGroupNatCardTorsionByPowEqPow
public import Nyll.ProCGroups.Abelian.AddCommGroupBasisZmodPow
public import Nyll.ProCGroups.Abelian.AddMonoidHomNsmulEqZeroApplyEq
public import Nyll.ProCGroups.Abelian.AddMonoidHomMemRangeSmulEqZero
public import Nyll.ProCGroups.Abelian.AddMonoidHomNatCardKerCompEqMul
public import Nyll.ProCGroups.Abelian.CharacterCardinalityTorsionFree
public import Nyll.ProCGroups.Abelian.CharacterDetection
public import Nyll.ProCGroups.Abelian.FiniteBidual
public import Nyll.ProCGroups.Abelian.FiniteCharacterCriterion
public import Nyll.ProCGroups.Abelian.FiniteFixedCharacters
public import Nyll.ProCGroups.Abelian.FiniteInvariantQuotients
public import Nyll.ProCGroups.Abelian.FinsuppListEqSumSingleSubSingle
public import Nyll.ProCGroups.Abelian.FullTateCharacters
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.ProCGroups.Abelian.FullTateModuleMap
public import Nyll.ProCGroups.Abelian.FullTateRestriction
public import Nyll.ProCGroups.Abelian.PowerQuotientAction
public import Nyll.ProCGroups.Abelian.PrimaryDetection
public import Nyll.ProCGroups.Abelian.PrimaryTorsion
public import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
public import Nyll.ProCGroups.Abelian.PrimePowerCharacters
public import Nyll.ProCGroups.Abelian.PrimeQuotients
public import Nyll.ProCGroups.Abelian.ProfiniteBidual
public import Nyll.ProCGroups.Abelian.ProfiniteCharacterCriterion
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Abelian.RestrictedTatePadic
public import Nyll.ProCGroups.Abelian.RestrictedTatePairingWeights
public import Nyll.ProCGroups.Abelian.RestrictedTateTorsionFree
public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Nyll.ProCGroups.Abelian.RootsOfUnityCharacterCriterion
public import Nyll.ProCGroups.Abelian.SubgroupCommutator
public import Nyll.ProCGroups.Abelian.SubmoduleFiniteTorsionByPow
public import Nyll.ProCGroups.Abelian.SubmoduleNatCardTorsionByQuotientEqPowFinrank
public import Nyll.ProCGroups.Abelian.SubtractionMonoidZsmulEqPrime
public import Nyll.ProCGroups.Abelian.SubtractionMonoidZsmulEqPrimeNsmul
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationConjugationContinuity
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationLimits
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationQuotientFaithfulness
public import Nyll.ProCGroups.Abelian.Transfer
public import Nyll.ProCGroups.Abelian.CardTorsionMulDivisible


public import Nyll.ProCGroups.Abelian.AbelianizedGeometricPreimage
public import Nyll.ProCGroups.Abelian.ArithmeticFirstQuotient
public import Nyll.ProCGroups.Abelian.CharacterFixedQuotients
public import Nyll.ProCGroups.Abelian.CoherentDisplacementFamilies
public import Nyll.ProCGroups.Abelian.ConjugationDifferenceIntersection
public import Nyll.ProCGroups.Abelian.ConstantAbelianizationDetection
public import Nyll.ProCGroups.Abelian.FiniteTransferSquare
public import Nyll.ProCGroups.Abelian.MarkedLocalDetection
public import Nyll.ProCGroups.Abelian.MaximalAbelianProP
public import Nyll.ProCGroups.Abelian.PrimaryFixedDetection
public import Nyll.ProCGroups.Abelian.PrimaryQuotientSplitting
public import Nyll.ProCGroups.Abelian.PrimeToAbelianRoots
public import Nyll.ProCGroups.Abelian.PrimeToRootsDetection
public import Nyll.ProCGroups.Abelian.SemilinearFixedCharacters
public import Nyll.ProCGroups.Abelian.SplitProcyclicAbelianization
public import Nyll.ProCGroups.Abelian.TopologicalTransferComparison
public import Nyll.ProCGroups.Abelian.TopologicalTransferNaturality
public import Nyll.ProCGroups.Abelian.TransferThroughCoverEquiv


/-!
# Abelian constructions

This aggregate module exposes topological abelianization, its functoriality, and its compatibility
with inverse limits.
-/
