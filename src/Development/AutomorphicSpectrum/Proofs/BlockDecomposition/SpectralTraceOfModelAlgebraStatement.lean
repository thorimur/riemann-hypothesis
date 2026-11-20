import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectral_trace_of_model_algebra : UModel → LocAlg → SpecTrace := by
  first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)
