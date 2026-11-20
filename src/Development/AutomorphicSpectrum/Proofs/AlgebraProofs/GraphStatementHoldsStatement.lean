import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_statement_holds : GraphStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graphStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.graphStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graphStatement <;> assumption)
