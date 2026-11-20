import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
