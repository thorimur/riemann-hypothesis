import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := by
  first | exact @GlobalTheory.SqTop.botExT_holds | exact GlobalTheory.SqTop.botExT_holds | (intros; apply GlobalTheory.SqTop.botExT_holds <;> assumption)
