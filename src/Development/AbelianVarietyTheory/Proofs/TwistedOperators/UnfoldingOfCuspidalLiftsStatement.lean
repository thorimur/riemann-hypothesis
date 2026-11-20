import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLifts
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_of_cuspidal_lifts : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := by
  first | exact @GlobalTheory.RowUnfLast.stepUnfold | exact GlobalTheory.RowUnfLast.stepUnfold | (intros; apply GlobalTheory.RowUnfLast.stepUnfold <;> assumption)
