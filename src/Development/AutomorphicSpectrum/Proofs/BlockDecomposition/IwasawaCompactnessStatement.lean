import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
