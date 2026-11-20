import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultIntegralPowerBound
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mult_integral_power_bound : ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  first | exact @GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | exact GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | (intros; apply GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le <;> assumption)
