import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_degree_of_intersection_and_resolution : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | exact GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree <;> assumption)
