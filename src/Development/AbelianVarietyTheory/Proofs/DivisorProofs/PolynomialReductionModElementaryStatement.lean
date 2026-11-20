import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialReductionModElementary
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_reduction_mod_elementary : ∀ (N : ℕ) (P : MvPolynomial (Fin N) ℝ), ∃ R ∈ Submodule.span ℝ {M : MvPolynomial (Fin N) ℝ | ∃ m : Fin N →₀ ℕ, (∀ i, m i ≤ (i : ℕ)) ∧ M = monomial m 1}, P - R ∈ Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) := by
  first | exact @GlobalTheory.ArtinSpan.artin_monomials_span | exact GlobalTheory.ArtinSpan.artin_monomials_span | (intros; apply GlobalTheory.ArtinSpan.artin_monomials_span <;> assumption)
