import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_modelCrit_chart_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n), IsArithVar P (n + 1) → IsGoodProj P Q → volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null <;> assumption)
