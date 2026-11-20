import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  first | exact @GlobalTheory.CompanionTheory.Equi.equi | exact GlobalTheory.CompanionTheory.Equi.equi | (intros; apply GlobalTheory.CompanionTheory.Equi.equi <;> assumption)
