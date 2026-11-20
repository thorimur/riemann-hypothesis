import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @GlobalTheory.WeilConv.weilConvergence | exact GlobalTheory.WeilConv.weilConvergence | (intros; apply GlobalTheory.WeilConv.weilConvergence <;> assumption)
