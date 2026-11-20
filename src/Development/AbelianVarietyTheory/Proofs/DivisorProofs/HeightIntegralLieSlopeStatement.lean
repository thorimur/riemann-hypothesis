import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightIntegralLieSlope
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_integral_lie_slope : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtIntSt := by
  first | exact @GlobalTheory.HeightParts.htIntSt_of_hypotheses | exact GlobalTheory.HeightParts.htIntSt_of_hypotheses | (intros; apply GlobalTheory.HeightParts.htIntSt_of_hypotheses <;> assumption)
