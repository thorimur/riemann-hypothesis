import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  first | exact @GlobalTheory.Published.arShift_of_arChange | exact GlobalTheory.Published.arShift_of_arChange | (intros; apply GlobalTheory.Published.arShift_of_arChange <;> assumption)
