import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleReality
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pole_reality : PoleReal := by
  first | exact @GlobalTheory.CompanionTheory.PoleBound.poleReal | exact GlobalTheory.CompanionTheory.PoleBound.poleReal | (intros; apply GlobalTheory.CompanionTheory.PoleBound.poleReal <;> assumption)
