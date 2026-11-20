import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernel
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_kernel_mem_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero <;> assumption)
