import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_pieces_of_intersection_and_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK <;> assumption)
