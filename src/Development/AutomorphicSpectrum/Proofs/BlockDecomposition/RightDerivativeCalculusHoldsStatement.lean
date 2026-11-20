import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_calculus_holds : PositivityTheory.RgBcC.RCalc := by
  first | exact @GlobalTheory.CompanionTheory.RCalc.rcalc | exact GlobalTheory.CompanionTheory.RCalc.rcalc | (intros; apply GlobalTheory.CompanionTheory.RCalc.rcalc <;> assumption)
