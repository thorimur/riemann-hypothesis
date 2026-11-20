import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | exact GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula <;> assumption)
