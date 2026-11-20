import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestTermLemmaReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_term_lemma_real : PositivityTheory.RgBcC.RealD.LemmaHT := by
  first | exact @GlobalTheory.CompanionTheory.SpinBound.lemmaHT | exact GlobalTheory.CompanionTheory.SpinBound.lemmaHT | (intros; apply GlobalTheory.CompanionTheory.SpinBound.lemmaHT <;> assumption)
