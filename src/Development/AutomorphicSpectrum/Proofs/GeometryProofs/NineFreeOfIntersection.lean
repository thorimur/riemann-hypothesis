import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystemStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfStatementsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem nineFree_of_intersection :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.ZhangDimensionPushDownGrassmannianHeightBounds := by
  intro hI hHS hBig hRes
  obtain ⟨-, -, -, -, hZ, hD⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_moriwaki hHS hBig
  exact ⟨hZ, hD, trivial, GlobalTheory.T.push_down_of_arith_intersection_system hI, GlobalTheory.T.grassmann_height_Z2_of_statements hI hHS hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
