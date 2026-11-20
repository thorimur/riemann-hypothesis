import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionStatementHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_statement_holds : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.Statement := by
  first | exact @GlobalTheory.GradedLines.statement | exact GlobalTheory.GradedLines.statement | (intros; apply GlobalTheory.GradedLines.statement <;> assumption)
