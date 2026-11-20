import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integrable_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK <;> assumption)
