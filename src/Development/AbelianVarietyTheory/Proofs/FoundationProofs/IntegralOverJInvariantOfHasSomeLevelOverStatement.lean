import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  first | exact @GlobalTheory.FN.integral_over_jT | exact GlobalTheory.FN.integral_over_jT | (intros; apply GlobalTheory.FN.integral_over_jT <;> assumption)
