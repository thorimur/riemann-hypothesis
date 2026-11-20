import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_unfolding : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideUnfold | exact GlobalTheory.CompanionTheory.RgEisSide.sideUnfold | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideUnfold <;> assumption)
