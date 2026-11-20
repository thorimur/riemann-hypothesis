import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DemaillyRegularisationEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionEstimateOfDualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightIntegralLieSlopeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundOfLieSlopeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntisymmetryFromPrismaticDieudonneStatement

namespace GlobalTheory.CovHt.KnownOf

open GlobalTheory.CovTop GlobalTheory.CovHt

theorem heightEstimates_of_lieSlope (hX : HypothesesXH) (h2 : Hypotheses2) (hH : HypothesesH) (hY : HypothesesY)
    (hSW : GlobalTheory.Published.ScholzeWeinsteinB) (hPD : GlobalTheory.Published.PoincareDeRhamDuality) (hL : GlobalTheory.LieHt.LieSlope)
    (hC : ∃ r, GlobalTheory.CovTest.Ch2Const r) : Known₂ where
  int := GlobalTheory.T.height_integral_lie_slope h2 hH hSW hL
  bd := GlobalTheory.T.height_bound_of_lie_slope h2 hH hSW hL
  up := GlobalTheory.DenseBoundedHeight.htUpSt h2 hH
  reg := GlobalTheory.T.demailly_regularisation_estimate h2 hH hY.dem
  test := GlobalTheory.T.test_function_estimate_of_duality hX h2 hH hY.alt hSW hY.perfd hPD hC
  anti := GlobalTheory.T.antisymmetry_from_prismatic_dieudonne h2 hH hY.alt hSW hY.perfd

end GlobalTheory.CovHt.KnownOf
