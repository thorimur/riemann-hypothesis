import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_height_constants : Top.Given → Out.WeilSt → Fl.FlatDegree → ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | exact GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given <;> assumption)
