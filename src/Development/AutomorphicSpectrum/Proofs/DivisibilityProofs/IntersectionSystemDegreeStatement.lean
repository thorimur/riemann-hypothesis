import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | exact GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem <;> assumption)
