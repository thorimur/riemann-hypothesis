import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSlopePointIntegrality
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_slope_point_integrality : LieSlope → PtInt → StepInt := by
  first | exact @GlobalTheory.HeightParts.stepInt_of_lieSlope | exact GlobalTheory.HeightParts.stepInt_of_lieSlope | (intros; apply GlobalTheory.HeightParts.stepInt_of_lieSlope <;> assumption)
