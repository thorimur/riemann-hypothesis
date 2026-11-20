import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3OfMoriwaki
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G3_of_moriwaki : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection | exact GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection <;> assumption)
