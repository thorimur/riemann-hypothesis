import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExcludedPrimesFewAndSmallAlongFamily
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excludedPrimes_few_and_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  first | exact @GlobalTheory.NLink.excOK_family | exact GlobalTheory.NLink.excOK_family | (intros; apply GlobalTheory.NLink.excOK_family <;> assumption)
