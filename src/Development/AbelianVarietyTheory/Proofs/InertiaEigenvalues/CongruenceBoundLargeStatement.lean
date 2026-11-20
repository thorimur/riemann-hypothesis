import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundLarge
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_bound_large : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), GlobalTheory.NFacts.Facts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  first | exact @GlobalTheory.NLinkE.main | exact GlobalTheory.NLinkE.main | (intros; apply GlobalTheory.NLinkE.main <;> assumption)
