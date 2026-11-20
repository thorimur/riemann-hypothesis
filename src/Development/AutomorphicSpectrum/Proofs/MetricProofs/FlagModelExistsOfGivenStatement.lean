import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_exists_of_given : Given → PB.FlagModelExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists <;> assumption)
