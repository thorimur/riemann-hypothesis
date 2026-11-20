import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_exists_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | exact GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.thmIExists <;> assumption)
