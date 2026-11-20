import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_tate_integral : Ad3.LR.C.TateInt := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.tateInt | exact GlobalTheory.CompanionTheory.RealTateConv.tateInt | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.tateInt <;> assumption)
