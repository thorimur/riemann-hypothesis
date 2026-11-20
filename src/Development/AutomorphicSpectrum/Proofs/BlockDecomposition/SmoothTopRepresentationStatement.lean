import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTopRepresentation
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_top_representation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V), IsSmooth τ → IsSmooth (topRep τ W) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep <;> assumption)
