import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_chart_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ), IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  first | exact @GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | exact GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | (intros; apply GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ <;> assumption)
