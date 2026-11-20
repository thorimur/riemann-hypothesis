import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_lattice_conj_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist <;> assumption)
