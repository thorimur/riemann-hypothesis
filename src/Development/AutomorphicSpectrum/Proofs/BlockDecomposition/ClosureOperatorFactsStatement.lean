import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  first | exact @GlobalTheory.CompanionTheory.FcCls.clsFacts | exact GlobalTheory.CompanionTheory.FcCls.clsFacts | (intros; apply GlobalTheory.CompanionTheory.FcCls.clsFacts <;> assumption)
