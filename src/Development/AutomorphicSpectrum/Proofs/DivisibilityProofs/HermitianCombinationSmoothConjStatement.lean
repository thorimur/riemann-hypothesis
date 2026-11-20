import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_combination_smooth_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | exact GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj <;> assumption)
