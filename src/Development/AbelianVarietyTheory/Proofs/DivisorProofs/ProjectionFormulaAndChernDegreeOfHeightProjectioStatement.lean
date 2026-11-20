import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectionFormulaAndChernDegree_of_heightProjection : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ArDegree := by
  first | exact @GlobalTheory.Published.arDegree_of_heightProjection | exact GlobalTheory.Published.arDegree_of_heightProjection | (intros; apply GlobalTheory.Published.arDegree_of_heightProjection <;> assumption)
