import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_and_coordinates_of_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord | exact GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord <;> assumption)
