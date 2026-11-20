import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  first | exact @GlobalTheory.FN.hasQ_of_periodic_bounded | exact GlobalTheory.FN.hasQ_of_periodic_bounded | (intros; apply GlobalTheory.FN.hasQ_of_periodic_bounded <;> assumption)
