import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSlopePointBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_slope_point_bound : Hypotheses2 → HypothesesH → LieSlope → PtBd → OmCmp → StepBd := by
  first | exact @GlobalTheory.HeightParts.BdProof.main | exact GlobalTheory.HeightParts.BdProof.main | (intros; apply GlobalTheory.HeightParts.BdProof.main <;> assumption)
