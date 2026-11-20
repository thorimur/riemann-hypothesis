import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfFamilyFacts
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusion_of_family_facts : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → FactsF Fm C CT → BoundAtTwoAndThreeForFamily Fm → ConclF Fm := by
  first | exact @GlobalTheory.NLinkClose.main | exact GlobalTheory.NLinkClose.main | (intros; apply GlobalTheory.NLinkClose.main <;> assumption)
