import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoBaseComponentShortPolynomialGenerator
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_base_component_short_polynomial_generator : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  first | exact @GlobalTheory.NoBase.noBase | exact GlobalTheory.NoBase.noBase | (intros; apply GlobalTheory.NoBase.noBase <;> assumption)
