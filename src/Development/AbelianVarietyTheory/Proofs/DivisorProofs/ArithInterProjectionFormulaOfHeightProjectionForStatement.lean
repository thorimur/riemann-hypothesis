import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionFor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArProj := by
  first | exact @GlobalTheory.Published.arProj_of_heightProjection | exact GlobalTheory.Published.arProj_of_heightProjection | (intros; apply GlobalTheory.Published.arProj_of_heightProjection <;> assumption)
