import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_section_good : PositivityTheory.RgEis.StdGood := by
  first | exact @GlobalTheory.CompanionTheory.StdGoodAd.stdGood | exact GlobalTheory.CompanionTheory.StdGoodAd.stdGood | (intros; apply GlobalTheory.CompanionTheory.StdGoodAd.stdGood <;> assumption)
