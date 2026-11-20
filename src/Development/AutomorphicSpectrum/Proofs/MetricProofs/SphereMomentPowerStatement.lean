import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPower
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_moment_power : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one <;> assumption)
