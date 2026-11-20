import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_provision_holds : Prov.An := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.prov_an | exact GlobalTheory.CompanionTheory.Ar.Link.prov_an | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.prov_an <;> assumption)
