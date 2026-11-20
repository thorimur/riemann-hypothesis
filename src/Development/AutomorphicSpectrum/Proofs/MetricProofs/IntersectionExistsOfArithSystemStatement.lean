import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_exists_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system <;> assumption)
