import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_span_twist_shift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω), c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | exact GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | (intros; apply GlobalTheory.CompanionTheory.Conductor.exists_conductor_section <;> assumption)
