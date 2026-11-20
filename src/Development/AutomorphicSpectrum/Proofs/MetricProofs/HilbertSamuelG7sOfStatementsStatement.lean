import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7sOfStatements
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G7s_of_statements : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArithmeticHilbertSamuelUpperBoundNumberField := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.smallSections_upper_of_moriwaki | exact GlobalTheory.CompanionTheory.Ar.Giv.smallSections_upper_of_moriwaki | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.smallSections_upper_of_moriwaki <;> assumption)
