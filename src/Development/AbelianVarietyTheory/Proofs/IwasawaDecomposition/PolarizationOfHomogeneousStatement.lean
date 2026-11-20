import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOfHomogeneous
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_of_homogeneous : ∀ (ι : Type) [Fintype ι] (B : Type) [AddCommGroup B] (w : ι → B) (f : B → ℝ) (d : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ), (∀ n : ι → ℤ, f (∑ i, n i • w i) = c * Ψ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ d)) → ∀ μ : Multiset ι, Multiset.card μ = d → polar f (μ.map w) = c * Ψ ((μ.map MvPolynomial.X).prod) := by
  first | exact @GlobalTheory.ShFam.PolarPowers.polar_eq_of_pow | exact GlobalTheory.ShFam.PolarPowers.polar_eq_of_pow | (intros; apply GlobalTheory.ShFam.PolarPowers.polar_eq_of_pow <;> assumption)
