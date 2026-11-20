import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartPrimElt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartSpecCount
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocAwaySpec
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldExistsInv
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBasisIsoFree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFreeSheafBasis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueTwo
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PIsoGlueTwo
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLocSectionsInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullInjLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomInjLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalChartLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMult
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOrderLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntermediateRingQuotLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLengthMapIdealLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleLocalQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleSpanMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalDomainDimTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotFinsum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotPrimes
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimesSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointVertDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount : GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.proof GroundTheory.Heights₂.Heights.Inter.ChartPrimElt.proof GroundTheory.Heights₂.Heights.Inter.LocAwaySpec.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ValuativeCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_GenericProjClosureDivisor : GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor.proof GroundTheory.Heights₂.Heights.NumbersDVR.TwistedDualGensExpress.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.joinTwoModels_holds : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleSpanMul.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocCyclePos.proof GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimesSpanSingleton.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalDomainDimTwo.proof GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.proof GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingNoetherian.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.joinPointFlagModel_holds : GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel.proof GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation.proof GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel.proof GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpModel.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpStrictTransform.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalizedQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.LengthMapIdealLe.proof GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpLocalChart.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMinimal.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalChartLength.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_PairBundleTrdeg : GroundTheory.Heights₂.Heights.NumbersDVR.PairBundleTrdeg.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.PairBundleTrdeg.proof GroundTheory.Heights₂.Heights.NumbersDVR.AdjoinTrdegAdd.proof GroundTheory.Heights₂.Heights.NumbersDVR.PairConeLinesIndep.proof GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomInjLoc : GroundTheory.Heights₂.Heights.Model.SpreadHomInjLoc.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadHomInjLoc.proof GroundTheory.Heights₂.Heights.Model.LocSectionsInj.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadGlue : GroundTheory.Heights₂.Heights.Model.SpreadGlue.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadGlue.proof GroundTheory.Heights₂.Heights.Model.GlueTwo.proof GroundTheory.Heights₂.Heights.Model.IsoGlueTwo.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_PullInjLoc : GroundTheory.Heights₂.Heights.Model.PullInjLoc.Statement :=
  @GroundTheory.Heights₂.Heights.Model.PullInjLoc.proof GroundTheory.Heights₂.Heights.Model.LocSectionsInj.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_GenericPullInj : GroundTheory.Heights₂.Heights.Model.GenericPullInj.Statement :=
  @GroundTheory.Heights₂.Heights.Model.GenericPullInj.proof GroundTheory.Heights₂.Heights.Model.GenericSectionsInj.proof GroundTheory.Heights₂.Heights.Model.PullbackBasis.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_BasisIsoFree.{u} : GroundTheory.Heights₂.Heights.Model.BasisIsoFree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.Model.BasisIsoFree.proof.{u} GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_ClearDenominators : GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement :=
  @GroundTheory.Heights₂.Heights.Model.ClearDenominators.of_open GroundTheory.Heights₂.Heights.Model.PullbackBasis.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.clearDenominators_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.ClearDenominators.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.ClearDenominators.of_open GroundTheory.Heights₂.Heights.Model.PullbackBasis.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.dominating_dvr_exists_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.DominatingDVR.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.DominatingDVR.of_open GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof
