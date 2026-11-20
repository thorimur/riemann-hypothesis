import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_height_Z2_of_inputs_and_Z2 : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | exact GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push <;> assumption)
