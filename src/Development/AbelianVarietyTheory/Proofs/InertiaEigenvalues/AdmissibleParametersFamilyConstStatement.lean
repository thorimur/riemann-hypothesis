import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parameters_family_const : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  first | exact @GlobalTheory.NLink.admissible_parameters_design_family | exact GlobalTheory.NLink.admissible_parameters_design_family | (intros; apply GlobalTheory.NLink.admissible_parameters_design_family <;> assumption)
