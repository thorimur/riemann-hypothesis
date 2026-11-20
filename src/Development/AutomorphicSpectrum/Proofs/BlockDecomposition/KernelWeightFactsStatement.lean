import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  first | exact @GlobalTheory.CompanionTheory.KerWord.kerW | exact GlobalTheory.CompanionTheory.KerWord.kerW | (intros; apply GlobalTheory.CompanionTheory.KerWord.kerW <;> assumption)
