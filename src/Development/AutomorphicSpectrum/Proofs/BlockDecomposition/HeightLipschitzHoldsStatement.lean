import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lipschitz_holds : PositivityTheory.RgEis.HtLip := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)
