import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_pullback_formula : GdegPull := by
  first | exact @GlobalTheory.CovTest.gdegPull | exact GlobalTheory.CovTest.gdegPull | (intros; apply GlobalTheory.CovTest.gdegPull <;> assumption)
