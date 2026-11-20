import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HsLinksOfMoriwaki
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3StarOfStatementsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7sOfStatementsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivityStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem hodgeIndex_of_intersection :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.HS := by
  intro hI hHS hBig hRes
  obtain ⟨g1, z1, z2, g6p, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_moriwaki hHS hBig
  exact ⟨z1, z2, g1, g6p, GlobalTheory.T.big_line_implies_height_positivity hBig, GlobalTheory.T.hodge_index_implies_height_bound hHS, GlobalTheory.T.hilbert_samuel_G7s_of_statements hI hHS hRes,
    GlobalTheory.T.hilbert_samuel_G3_of_moriwaki hHS hBig, GlobalTheory.T.hilbert_samuel_G3Star_of_statements hI hHS hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
