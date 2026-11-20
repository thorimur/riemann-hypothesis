import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianZeroOfLeviZero
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_zero_of_levi_zero : ∀ {e : ℕ} (G : (Fin e → ℂ) → ℝ) (τ : ReciprocityTheory.L2DbarEstimates.V e → ReciprocityTheory.L2DbarEstimates.V e) {U : Set (ReciprocityTheory.L2DbarEstimates.V e)} {x : ReciprocityTheory.L2DbarEstimates.V e}, IsOpen U → x ∈ U → DifferentiableOn ℂ τ U → ContDiffAt ℝ 2 G ((FinChart.toV e).symm (τ x)) → (∀ w, levi G ((FinChart.toV e).symm (τ x)) w = 0) → ReciprocityTheory.L2DbarEstimates.cHess e (fun v => ((G ((FinChart.toV e).symm (τ v)) : ℝ) : ℂ)) x = 0 := by
  first | exact @GlobalTheory.HessZero.cHess_comp_eq_zero_of_levi_zero | exact GlobalTheory.HessZero.cHess_comp_eq_zero_of_levi_zero | (intros; apply GlobalTheory.HessZero.cHess_comp_eq_zero_of_levi_zero <;> assumption)
