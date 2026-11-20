import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExists
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.modelEx_main | exact GlobalTheory.CompanionTheory.ModelS.modelEx_main | (intros; apply GlobalTheory.CompanionTheory.ModelS.modelEx_main <;> assumption)
