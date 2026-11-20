import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHolds
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_statement_holds : TateSt := by
  first | exact @GlobalTheory.FlatModel.tateSt | exact GlobalTheory.FlatModel.tateSt | (intros; apply GlobalTheory.FlatModel.tateSt <;> assumption)
