import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceOfCuspidalLifts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_independence_of_cuspidal_lifts : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.LinK := by
  first | exact @GlobalTheory.RowTest.linK | exact GlobalTheory.RowTest.linK | (intros; apply GlobalTheory.RowTest.linK <;> assumption)
