import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantTorusLtTop
open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_torus_lt_top : ∀ σ : ℝ, 0 < σ → σ < 1 → Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ 4) ∧ (∀ h, 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) ∧
    ∫⁻ h : Ad3.K.LC.M22, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.PerUC.GaInt.ga_integrable | exact GlobalTheory.CompanionTheory.PerUC.GaInt.ga_integrable | (intros; apply GlobalTheory.CompanionTheory.PerUC.GaInt.ga_integrable <;> assumption)
