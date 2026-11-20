import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7OfMoriwaki
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G7_of_moriwaki : MoriwakiHSStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS | exact GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS <;> assumption)
