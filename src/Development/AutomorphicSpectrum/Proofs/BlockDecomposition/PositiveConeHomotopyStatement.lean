import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_cone_homotopy : PositivityTheory.RgBcC.Homot := by
  first | exact @GlobalTheory.CompanionTheory.SuperHomot.homot | exact GlobalTheory.CompanionTheory.SuperHomot.homot | (intros; apply GlobalTheory.CompanionTheory.SuperHomot.homot <;> assumption)
