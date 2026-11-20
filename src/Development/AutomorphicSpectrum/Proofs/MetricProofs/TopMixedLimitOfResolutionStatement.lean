import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_mixed_limit_of_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.TopNMixedLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | exact GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit <;> assumption)
