import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveStatementHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_statement_holds : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement | exact GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement <;> assumption)
