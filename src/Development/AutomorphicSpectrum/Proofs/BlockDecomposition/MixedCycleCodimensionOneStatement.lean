import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_codimension_one : GlobalTheory.CompanionTheory.MixZ.CodimOne := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.codimOne_holds | exact GlobalTheory.CompanionTheory.MixZ.codimOne_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.codimOne_holds <;> assumption)
