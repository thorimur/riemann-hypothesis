import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionEstimateOfDuality
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
theorem _root_.GlobalTheory.T.test_function_estimate_of_duality : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → PoincareDeRhamDuality → (∃ r, Ch2Const r) → TestSt := by
  first | exact @GlobalTheory.TestClassObj.main | exact GlobalTheory.TestClassObj.main | (intros; apply GlobalTheory.TestClassObj.main <;> assumption)
