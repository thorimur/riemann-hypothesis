import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_term_good : HGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisHGood.hGood | exact GlobalTheory.CompanionTheory.RgEisHGood.hGood | (intros; apply GlobalTheory.CompanionTheory.RgEisHGood.hGood <;> assumption)
