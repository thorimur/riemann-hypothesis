import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorNormal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_normal : PositivityTheory.RgBcC.GelN := by
  first | exact @GlobalTheory.CompanionTheory.GelLevi.gelN | exact GlobalTheory.CompanionTheory.GelLevi.gelN | (intros; apply GlobalTheory.CompanionTheory.GelLevi.gelN <;> assumption)
