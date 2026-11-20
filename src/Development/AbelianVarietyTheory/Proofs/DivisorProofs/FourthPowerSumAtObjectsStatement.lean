import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourthPowerSumAtObjects
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
theorem _root_.GlobalTheory.T.fourth_power_sum_at_objects : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → OnObj fun _ O _ _ _ _ => PrimeLocalCondition O.Y := by
  first | exact @GlobalTheory.Whole4.main | exact GlobalTheory.Whole4.main | (intros; apply GlobalTheory.Whole4.main <;> assumption)
