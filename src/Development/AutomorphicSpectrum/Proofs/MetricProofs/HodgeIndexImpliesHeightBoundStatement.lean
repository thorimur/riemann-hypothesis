import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeIndexImpliesHeightBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_index_implies_height_bound : MoriwakiHSStatement → ArithmeticHilbertSamuelUpperBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | exact GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki <;> assumption)
