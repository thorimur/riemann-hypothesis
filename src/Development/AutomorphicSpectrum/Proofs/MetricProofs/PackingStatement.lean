import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingAlt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing' : PackingStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.packing | exact GlobalTheory.CompanionTheory.Ar.Small.packing | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.packing <;> assumption)
