import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SideZeroOfLocalProperness

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

theorem headBridge_of_rest (hPr : ProperDomP) (hW : WordSmooth) (h1 : Side1) : LevelPointCoordinates.HeadBridge :=
  headBridge_of Formalism.FourierDecayAlt.P.rules_eq hW pts curveSmooth (supp_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr)
    (Formalism.FourierDecayAlt.P.SliceIntegralLemmas.side_zero_of_local_properness hPr) h1 Formalism.FourierDecayAlt.P.one_variable_letters_under_integral

end Formalism.FourierDecayAlt.P.CutHB
