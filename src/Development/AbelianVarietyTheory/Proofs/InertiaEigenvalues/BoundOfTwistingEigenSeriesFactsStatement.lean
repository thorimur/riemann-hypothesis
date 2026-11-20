import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundOfTwistingEigenSeriesFacts
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bound_of_twisting_eigen_series_facts : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), GlobalTheory.NFacts.Facts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → PairedCharacterCondition.aux₃ (D := D) (8 * (CT : ℝ)) CT := by
  first | exact @GlobalTheory.NormFromFacts.main | exact GlobalTheory.NormFromFacts.main | (intros; apply GlobalTheory.NormFromFacts.main <;> assumption)
