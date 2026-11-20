import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreAction
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_fibre_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z), IsSmooth ρ₀ → IsSmooth (fibAct t ρ₀) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct <;> assumption)
