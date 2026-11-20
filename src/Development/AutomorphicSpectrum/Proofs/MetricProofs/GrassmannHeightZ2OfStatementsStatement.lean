import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfStatements
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_height_Z2_of_statements : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_systems | exact GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_systems | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_systems <;> assumption)
