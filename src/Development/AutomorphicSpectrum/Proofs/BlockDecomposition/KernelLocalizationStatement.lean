import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_localization : PositivityTheory.RgBcC.Fc.KerLoc := by
  first | exact @GlobalTheory.CompanionTheory.WaveLoc.kerLoc | exact GlobalTheory.CompanionTheory.WaveLoc.kerLoc | (intros; apply GlobalTheory.CompanionTheory.WaveLoc.kerLoc <;> assumption)
