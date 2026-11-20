import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentDerivative
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem jfSmoothBuilt_of_chart (hE : ChartEqs) (hR : EllRegW) : JfSmoothBuilt :=
  jfSmoothBuilt_of_rest nilpotent_derivative group_equations_post_holds smooth_of_coefficients_holds hE hR

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

namespace Formalism.FourierDecayAlt.P.CutMP

end Formalism.FourierDecayAlt.P.CutMP
