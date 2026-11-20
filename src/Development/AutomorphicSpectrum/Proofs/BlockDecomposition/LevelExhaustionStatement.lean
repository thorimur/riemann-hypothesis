import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
