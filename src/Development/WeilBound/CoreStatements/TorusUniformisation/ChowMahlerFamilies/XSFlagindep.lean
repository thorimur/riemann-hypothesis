import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational

namespace PositivityTheory.Xgn.A_s_flagindep

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem closureModel : GenericProjClosureModel.Statement :=
  GenericProjClosureModel.proof TwistedDualGensExist.proof
    (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
      (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
    (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)

theorem flagClosureModel : SegreFlagClosureModel.Statement :=
  SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)

theorem of_items (hC2 : VerticalDivisorsCommute.Statement.{0}) (hPull : PairNumberPullback.Statement)
    (hCut : SegreFlagClosureCut.Statement) : FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof hC2
  have hSP := SegreFlagClosurePullback.proof hPull hPE flagClosureModel PairNumberRelabel.proof
    VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE flagClosureModel hCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE closureModel hSCN)
    SymmetricSpanHsymm.proof

end PositivityTheory.Xgn.A_s_flagindep
