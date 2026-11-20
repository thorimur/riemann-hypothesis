import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGrassmannPushOfInputs
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_grassmann_push_of_inputs : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.FlagGrassPush.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush | exact GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush <;> assumption)
