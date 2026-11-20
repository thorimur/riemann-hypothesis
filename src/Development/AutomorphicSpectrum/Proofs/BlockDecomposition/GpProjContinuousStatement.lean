import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | exact GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | (intros; apply GlobalTheory.CompanionTheory.BZMir.continuous_gpProj <;> assumption)
