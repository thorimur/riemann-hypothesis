import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typicalCurveEigenspace_and_basisExists : TypicalCurveEigenspace ∧ TypicalCurveBasisExists := by
  first | exact @GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | exact GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | (intros; apply GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases <;> assumption)
