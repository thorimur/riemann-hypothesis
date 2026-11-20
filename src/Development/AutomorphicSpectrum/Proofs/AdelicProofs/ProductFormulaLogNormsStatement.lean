import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNorms
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_log_norms : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧ (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | exact GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings <;> assumption)
