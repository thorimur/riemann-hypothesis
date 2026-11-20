import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3StarOfStatements
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G3Star_of_statements : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.hilbert_samuel_G3Star_of_systems | exact GlobalTheory.CompanionTheory.Ar.Giv.hilbert_samuel_G3Star_of_systems | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.hilbert_samuel_G3Star_of_systems <;> assumption)
