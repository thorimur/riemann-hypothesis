import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtraBoundOfTwistingEigenFacts
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_bound_of_twisting_eigen_facts : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), GlobalTheory.NFacts.Facts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → Extra D C CT := by
  first | exact @GlobalTheory.ExtraFromFacts.main | exact GlobalTheory.ExtraFromFacts.main | (intros; apply GlobalTheory.ExtraFromFacts.main <;> assumption)
