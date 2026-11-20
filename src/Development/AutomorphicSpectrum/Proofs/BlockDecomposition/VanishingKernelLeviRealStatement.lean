import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanishingKernelLeviReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_kernel_levi_real : PositivityTheory.RgBcC.RealD.VanKL := by
  first | exact @GlobalTheory.CompanionTheory.KostL.vanKL | exact GlobalTheory.CompanionTheory.KostL.vanKL | (intros; apply GlobalTheory.CompanionTheory.KostL.vanKL <;> assumption)
