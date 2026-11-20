import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxLength_localInvariants_twisted_fractionModInteger_le : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) → ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  first | exact @GlobalTheory.InvariantsKO.main | exact GlobalTheory.InvariantsKO.main | (intros; apply GlobalTheory.InvariantsKO.main <;> assumption)
