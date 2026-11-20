import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCharpolyRootLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem FibreNormDehomRoots.full : FibreNormDehomRoots.Statement :=
  FibreNormDehomRoots.proof
    (PullFormsGeneric.proof
      (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof))
    PullSectionIntegral.proof CharpolyRootLift.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
