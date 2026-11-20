import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumRelabel

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
