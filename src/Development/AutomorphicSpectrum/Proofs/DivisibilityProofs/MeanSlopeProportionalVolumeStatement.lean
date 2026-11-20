import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolume
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_slope_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | exact GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq <;> assumption)
