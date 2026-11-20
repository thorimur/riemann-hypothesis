import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackInputsOfStatements
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_inputs_of_statements : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackInputs_of_hypotheses | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackInputs_of_hypotheses | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackInputs_of_hypotheses <;> assumption)
