import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | exact GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.asmSpeed <;> assumption)
