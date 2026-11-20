import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime : GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.proof GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly.full GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound GroundTheory.Heights₂.Heights.ImageDimLe.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre : GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.Statement :=
  @GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.proof GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover
