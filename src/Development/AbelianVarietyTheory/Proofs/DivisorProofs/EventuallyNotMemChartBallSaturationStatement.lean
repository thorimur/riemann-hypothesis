import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_not_mem_chartBall_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) → ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b) := by
  first | exact @GlobalTheory.SaturationClosed.eventually_not_mem_saturation | exact GlobalTheory.SaturationClosed.eventually_not_mem_saturation | (intros; apply GlobalTheory.SaturationClosed.eventually_not_mem_saturation <;> assumption)
