import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_point_height_degree : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple <;> assumption)
