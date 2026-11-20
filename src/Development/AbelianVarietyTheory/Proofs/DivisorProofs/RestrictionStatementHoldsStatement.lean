import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionStatementHolds
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_statement_holds : RestrictSt := by
  first | exact @GlobalTheory.FlatModel.restrictSt | exact GlobalTheory.FlatModel.restrictSt | (intros; apply GlobalTheory.FlatModel.restrictSt <;> assumption)
