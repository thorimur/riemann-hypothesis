import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semi_abelian_statement_holds : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds <;> assumption)
