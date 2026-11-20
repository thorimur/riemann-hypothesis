import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GeneratedLineBundleNefOnFibres
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_line_bundle_nef_on_fibres : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.nefOnFibres_of_generatesOn | exact GlobalTheory.CompanionTheory.Ar.Giv.nefOnFibres_of_generatesOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.nefOnFibres_of_generatesOn <;> assumption)
