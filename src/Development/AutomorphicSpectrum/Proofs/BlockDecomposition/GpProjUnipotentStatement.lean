import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) → (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  first | exact @GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | exact GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.GpUnip.gpProj_unip <;> assumption)
