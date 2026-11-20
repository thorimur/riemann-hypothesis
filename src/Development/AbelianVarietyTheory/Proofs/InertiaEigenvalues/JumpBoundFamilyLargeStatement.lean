import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLarge
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_bound_family_large : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x), GlobalTheory.NFacts.Facts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  first | exact @GlobalTheory.LargeJumps.jump_bound_of_facts_large_family | exact GlobalTheory.LargeJumps.jump_bound_of_facts_large_family | (intros; apply GlobalTheory.LargeJumps.jump_bound_of_facts_large_family <;> assumption)
