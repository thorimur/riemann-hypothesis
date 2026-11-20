import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operators_commute : PositivityTheory.RgBcC.GelComm := by
  first | exact @GlobalTheory.CompanionTheory.GelC.gelComm | exact GlobalTheory.CompanionTheory.GelC.gelComm | (intros; apply GlobalTheory.CompanionTheory.GelC.gelComm <;> assumption)
