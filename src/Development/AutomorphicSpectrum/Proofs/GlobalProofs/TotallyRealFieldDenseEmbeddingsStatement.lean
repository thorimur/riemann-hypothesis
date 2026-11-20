import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_field_dense_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ), 0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx <;> assumption)
