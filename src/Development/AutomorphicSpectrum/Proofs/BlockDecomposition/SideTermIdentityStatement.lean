import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_identity : StdGood → BdetLaw → SideOf := by
  first | exact @GlobalTheory.CompanionTheory.MirSides.sideOf | exact GlobalTheory.CompanionTheory.MirSides.sideOf | (intros; apply GlobalTheory.CompanionTheory.MirSides.sideOf <;> assumption)
