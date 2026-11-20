import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeIndexOfIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_index_of_intersection : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.HS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.hodgeIndex_of_intersection | exact GlobalTheory.CompanionTheory.Ar.Link.hodgeIndex_of_intersection | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.hodgeIndex_of_intersection <;> assumption)
