import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_of_epstein_conv : EpConv → ZetaK := by
  first | exact @GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | exact GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | (intros; apply GlobalTheory.CompanionTheory.ZetaAlongK.zetaK <;> assumption)
